// Reconstruct and verify the exact Git source before executing one canonical
// job. Native custody and output evidence are authenticated by the finalizer.
import {createHash} from 'node:crypto'
import {execFileSync, spawnSync} from 'node:child_process'
import {closeSync, existsSync, lstatSync, mkdirSync, mkdtempSync, openSync, readFileSync, realpathSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {dirname, isAbsolute, join, sep} from 'node:path'
import {pathToFileURL} from 'node:url'

const sha256 = (data: Buffer | string) => createHash('sha256').update(data).digest('hex')
const sha1 = /^[0-9a-f]{40}$/
const sha256pattern = /^[0-9a-f]{64}$/
type Repository = {path: string, commit: string, tree: string, archive: string, archiveSha256: string}
type Manifest = {commit: string, tree: string, suiteSha256: string, repositories: Repository[], definitions: Record<string, string>}
function safePath(path: unknown, allowDot = false): path is string {
  return typeof path === 'string' && (allowDot && path === '.' || !!path && !isAbsolute(path) && !path.includes('\\') && !path.includes('\0') && path.split('/').every(p => p !== '' && p !== '.' && p !== '..' && p !== '.git'))
}
function inside(path: string, root: string): boolean { return path === root || path.startsWith(root + sep) }

// Narrow ustar reader: the only permitted archive member is a regular file
// named objects.pack. No tar extraction, hard links, symlinks or path traversal.
export function readPackTar(tar: Buffer): Buffer {
  if (tar.length < 1536 || tar.length % 512) throw Error('invalid tar length')
  const header = tar.subarray(0, 512)
  const text = (start: number, end: number) => header.subarray(start, end).toString('utf8').replace(/\0.*$/s, '')
  if (text(0, 100) !== 'objects.pack' || text(345, 500) !== '' || ![0, 48].includes(header[156]!)) throw Error('invalid archive member')
  const octal = (start: number, end: number) => {
    const value = text(start, end).trim()
    if (!/^[0-7]+$/.test(value)) throw Error('invalid tar number')
    return parseInt(value, 8)
  }
  const checksum = octal(148, 156)
  let actual = 0
  for (let i = 0; i < 512; i++) actual += i >= 148 && i < 156 ? 32 : header[i]!
  if (actual !== checksum) throw Error('invalid tar checksum')
  const size = octal(124, 136)
  const end = 512 + size, paddedEnd = 512 + Math.ceil(size / 512) * 512
  if (!Number.isSafeInteger(size) || end > tar.length || paddedEnd + 1024 > tar.length) throw Error('truncated tar')
  for (let i = end; i < tar.length; i++) if (tar[i] !== 0) throw Error('unexpected archive member or padding')
  return tar.subarray(512, end)
}

export async function worker(inputDir: string, manifestHash: string, jobName: string): Promise<number> {
  if (!sha256pattern.test(manifestHash) || !/^[A-Za-z0-9][A-Za-z0-9._-]*$/.test(jobName)) throw Error('invalid worker arguments')
  const output = process.env.SUPERCOMPUTER_OUTPUT_DIR
  if (!output || !isAbsolute(output)) throw Error('missing output directory')
  const bytes = readFileSync(join(inputDir, 'manifest.json'))
  if (sha256(bytes) !== manifestHash) throw Error('manifest hash mismatch')
  const manifest = JSON.parse(bytes.toString('utf8')) as Manifest
  if (!sha1.test(manifest.commit) || !sha1.test(manifest.tree) || !sha256pattern.test(manifest.suiteSha256) || !Array.isArray(manifest.repositories) || !manifest.repositories.length || !manifest.definitions || !sha256pattern.test(manifest.definitions[jobName] || '')) throw Error('invalid manifest')
  const root = mkdtempSync(join(tmpdir(), 'full-gate-'))
  if (inside(realpathSync(root), realpathSync(output)) || inside(realpathSync(output), realpathSync(root))) throw Error('temporary source overlaps output')
  const source = join(root, 'source')
  const gitEnv: NodeJS.ProcessEnv = {...process.env, GIT_CONFIG_NOSYSTEM: '1', GIT_CONFIG_GLOBAL: '/dev/null', GIT_TERMINAL_PROMPT: '0', GIT_OPTIONAL_LOCKS: '0'}
  for (const key of Object.keys(gitEnv)) if (/^GIT_(DIR|WORK_TREE|INDEX_FILE|OBJECT_DIRECTORY|ALTERNATE_OBJECT_DIRECTORIES|COMMON_DIR|CONFIG_COUNT)$/.test(key)) delete gitEnv[key]
  const git = (cwd: string, args: string[], input?: Buffer): Buffer => execFileSync('git', ['-c', 'core.hooksPath=/dev/null', '-c', 'core.autocrlf=false', ...args], {cwd, env: gitEnv, input, maxBuffer: 512 * 1024 * 1024})
  const text = (cwd: string, ...args: string[]) => git(cwd, args).toString('utf8').trim()
  try {
    const records = [...manifest.repositories]
    const first = records[0]!
    if (first.path !== '.' || first.commit !== manifest.commit || first.tree !== manifest.tree) throw Error('root identity mismatch')
    const seen = new Set<string>()
    const expectedLinks = new Map<string, string>()
    for (const [index, record] of records.entries()) {
      if (!safePath(record.path, index === 0) || !sha1.test(record.commit) || !sha1.test(record.tree) || !safePath(record.archive) || record.archive.includes('/') || !sha256pattern.test(record.archiveSha256) || seen.has(record.path)) throw Error('invalid repository record')
      seen.add(record.path)
      if (index && expectedLinks.get(record.path) !== record.commit) throw Error(`unmatched submodule: ${record.path}`)
      const dir = index ? join(source, record.path) : source
      if (index) {
        const parent = realpathSync(dirname(dir))
        if (!inside(parent, source)) throw Error('submodule path escapes source')
        if (existsSync(dir) && (lstatSync(dir).isSymbolicLink() || !lstatSync(dir).isDirectory())) throw Error('unsafe submodule destination')
      }
      mkdirSync(dir, {recursive: true})
      const archive = readFileSync(join(inputDir, record.archive))
      if (sha256(archive) !== record.archiveSha256) throw Error(`archive mismatch: ${record.path}`)
      const pack = readPackTar(archive)
      git(dir, ['init', '-q', '--object-format=sha1'])
      git(dir, ['index-pack', '--stdin'], pack)
      if (text(dir, 'rev-parse', `${record.commit}^{tree}`) !== record.tree) throw Error(`tree mismatch: ${record.path}`)
      // The pack intentionally omits parents. Mark this commit shallow before
      // checkout, so normal Git commands never need the rest of history.
      writeFileSync(join(dir, '.git', 'shallow'), record.commit + '\n')
      git(dir, ['update-ref', 'HEAD', record.commit])
      git(dir, ['checkout', '-q', '--force', record.commit])
      const rows = git(dir, ['ls-tree', '-rz', '--full-tree', record.commit]).toString('utf8').split('\0').filter(Boolean)
      for (const row of rows) {
        const match = /^160000 commit ([0-9a-f]{40})\t(.+)$/.exec(row)
        if (!match) continue
        const path = record.path === '.' ? match[2]! : `${record.path}/${match[2]!}`
        if (!safePath(path) || expectedLinks.has(path)) throw Error('invalid gitlink')
        expectedLinks.set(path, match[1]!)
      }
      if (text(dir, 'rev-parse', 'HEAD') !== record.commit || text(dir, 'write-tree') !== record.tree) throw Error('reconstructed repository mismatch')
    }
    for (const path of expectedLinks.keys()) if (!seen.has(path)) throw Error(`missing submodule: ${path}`)
    for (const record of [...records].reverse()) {
      const dir = record.path === '.' ? source : join(source, record.path)
      if (text(dir, 'status', '--porcelain=v1', '--untracked-files=all', '--ignore-submodules=none')) throw Error(`dirty reconstructed repository: ${record.path}`)
    }
    const suiteBytes = readFileSync(join(source, 'supercomputer/suite.json'))
    if (sha256(suiteBytes) !== manifest.suiteSha256) throw Error('suite mismatch')
    const suite = JSON.parse(suiteBytes.toString('utf8'))
    if (!Array.isArray(suite)) throw Error('invalid suite')
    const matches = suite.filter((job: {name?: unknown}) => job.name === jobName)
    if (matches.length !== 1) throw Error('missing or duplicate canonical job')
    const job = matches[0]
    const contract = await import(pathToFileURL(join(source, 'scripts/release-ci/full-gate-contract.ts')).href)
    if (contract.canonicalJobHash(job) !== manifest.definitions[jobName]) throw Error('definition mismatch')
    if (typeof job.cmd !== 'string' || !job.cmd || !safePath(job.cwd ?? '.', true)) throw Error('unsafe canonical command or cwd')
    const cwd = realpathSync(join(source, job.cwd ?? '.'))
    if (!inside(cwd, source)) throw Error('cwd escapes source')
    if (job.timeout !== undefined && (typeof job.timeout !== 'number' || !Number.isFinite(job.timeout) || job.timeout <= 0)) throw Error('invalid timeout')
    // The reconstructed checkout must resolve its own pinned dependencies, not
    // an unrelated node_modules from the transport tree or the reusable image.
    const dependencyLog = openSync(join(output, 'dependency-install.log'), 'wx')
    try {
      const install = spawnSync('bun', ['install', '--frozen-lockfile'], {cwd: source, env: process.env, stdio: ['ignore', dependencyLog, dependencyLog], timeout: 300_000})
      if (install.error || install.signal || install.status !== 0) throw Error('pinned dependency installation failed')
    } finally { closeSync(dependencyLog) }
    for (const record of [...records].reverse()) {
      const dir = record.path === '.' ? source : join(source, record.path)
      if (text(dir, 'status', '--porcelain=v1', '--untracked-files=all', '--ignore-submodules=none')) throw Error('dependency setup changed tracked source')
    }
    const submodules = Object.fromEntries(records.slice(1).map(item => [item.path, item.commit]))
    writeFileSync(join(output, 'PROVISIONED.json'), JSON.stringify({commit: manifest.commit, tree: manifest.tree, suiteSha256: manifest.suiteSha256, provisioningSha256: manifestHash, vendorPins: submodules, definitionSha256: manifest.definitions[jobName]}) + '\n', {flag: 'wx'})
    const stdout = openSync(join(output, 'stdout.log'), 'wx'), stderr = openSync(join(output, 'stderr.log'), 'wx')
    let result: ReturnType<typeof spawnSync>
    try {
      const args = job.timeout === undefined ? ['-c', job.cmd] : ['--signal=KILL', `${job.timeout}s`, 'bash', '-c', job.cmd]
      result = spawnSync(job.timeout === undefined ? 'bash' : 'timeout', args, {cwd, env: process.env, stdio: ['ignore', stdout, stderr]})
    } finally { closeSync(stdout); closeSync(stderr) }
    const code = result.status ?? 128
    writeFileSync(join(output, 'COMMAND-RESULT.json'), JSON.stringify({name: jobName, command: job.cmd, cwd: job.cwd ?? '.', code, signal: result.signal, error: result.error?.message ?? null}) + '\n', {flag: 'wx'})
    return code
  } finally { rmSync(root, {recursive: true, force: true}) }
}

if (import.meta.main) {
  const [input, hash, name] = process.argv.slice(2)
  if (!input || !hash || !name || process.argv.length !== 5) {
    console.error('usage: full-gate-worker INPUT MANIFEST_SHA256 JOB_NAME'); process.exitCode = 1
  } else worker(input, hash, name).then(code => { process.exitCode = code }, error => { console.error(error); process.exitCode = 1 })
}
