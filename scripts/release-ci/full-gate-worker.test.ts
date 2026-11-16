import {expect, test} from 'bun:test'
import {createHash} from 'node:crypto'
import {execFileSync, spawnSync} from 'node:child_process'
import {copyFileSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, utimesSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {delimiter, join} from 'node:path'
import {prepare} from './full-gate-runner'
import {diagnosticEnvironment, keyedSources, worker} from './full-gate-worker'

test('keyed source evidence requires the keyed job and a fresh regular file', () => {
  const root = mkdtempSync(join(tmpdir(), 'keyed-source-')), path = join(root, 'Keyed.lean')
  try {
    const started = Date.now() - 10_000, source = '-- prefix\ndef outbox_machine := 42\n'
    expect(keyedSources('lean-keyed', root, started)).toEqual([])
    writeFileSync(path, source)
    expect(keyedSources('lean-keyed', root, started)).toEqual([{file: 'Keyed.lean', source}])
    expect(keyedSources('other', root, started)).toEqual([])
    utimesSync(path, new Date(started - 5000), new Date(started - 5000))
    expect(keyedSources('lean-keyed', root, started)).toEqual([])
    rmSync(path); symlinkSync('missing', path)
    expect(() => keyedSources('lean-keyed', root, started)).toThrow('unsafe Keyed source file')
    rmSync(path); mkdirSync(path)
    expect(() => keyedSources('lean-keyed', root, started)).toThrow('unsafe Keyed source file')
  } finally { rmSync(root, {recursive: true, force: true}) }
})

test('full Lean diagnostics survive canonical tail filters without masking the compiler exit', () => {
  const root = mkdtempSync(join(tmpdir(), 'full-gate-diagnostics-'))
  try {
    const bin = join(root, 'real-bin'); mkdirSync(bin)
    writeFileSync(join(bin, 'lean'), '#!/bin/bash\nprintf "First.lean:1:1: error: first\\nLast.lean:2:1: error: last\\n"\nprintf "stderr-diagnostic\\n" >&2\nexit 7\n', {mode: 0o700})
    const capture = diagnosticEnvironment(root, root, {...process.env, PATH: bin + delimiter + process.env.PATH})
    const result = spawnSync('bash', ['-c', 'lean 2>&1 | tail -1; exit "${PIPESTATUS[0]}"'], {cwd: root, env: capture.env, encoding: 'utf8'})
    expect(result.status).toBe(7)
    expect(result.stdout).toBe('stderr-diagnostic\n')
    expect(capture.readLogs()).toEqual(['First.lean:1:1: error: first\nLast.lean:2:1: error: last\nstderr-diagnostic\n'])
  } finally { rmSync(root, {recursive: true, force: true}) }
})

test('diagnostic recording preserves axiom-gate refusals and captures every refusal', () => {
  const root = mkdtempSync(join(tmpdir(), 'full-gate-axioms-'))
  try {
    const bin = join(root, 'real-bin'); mkdirSync(bin)
    writeFileSync(join(bin, 'lean'), '#!/bin/bash\nprintf "\\x27bad\\x27 depends on axioms: [sorryAx]\\n"\n', {mode: 0o700})
    writeFileSync(join(root, 'Bad.lean'), 'theorem bad : True := by sorry\n#print axioms bad\n')
    const original: NodeJS.ProcessEnv = {...process.env, PATH: bin + delimiter + process.env.PATH}
    delete original.GDP_RELEASE_LEAN_LOGS
    const command = join(import.meta.dir, '../lean-gate/lean')
    const ordinary = spawnSync(command, ['Bad.lean'], {cwd: root, env: original, encoding: 'utf8'})
    const capture = diagnosticEnvironment(root, root, original)
    const recorded = spawnSync(command, ['Bad.lean'], {cwd: root, env: capture.env, encoding: 'utf8'})
    expect(ordinary.status).toBe(1)
    expect(recorded.status).toBe(ordinary.status)
    expect(recorded.stdout).toBe(ordinary.stdout)
    expect(capture.readLogs().join('\n')).toContain('axiom-gate:')
    expect(capture.readLogs().join('\n')).toContain('sorryAx')
  } finally { rmSync(root, {recursive: true, force: true}) }
})

const digest = (bytes: Buffer) => createHash('sha256').update(bytes).digest('hex')
async function refuses(promise: Promise<number>, message: string): Promise<void> {
  try { await promise } catch (error) {
    expect(error).toBeInstanceOf(Error)
    if (error instanceof Error) expect(error.message).toContain(message)
    return
  }
  throw Error('worker unexpectedly accepted invalid input')
}

test('opaque Git packs retain C sources and pinned submodules; tampering fails closed', async () => {
  const base = mkdtempSync(join(tmpdir(), 'full-gate-roundtrip-'))
  const previousOutput = process.env.SUPERCOMPUTER_OUTPUT_DIR
  const git = (cwd: string, ...args: string[]) => execFileSync('git', args, {
    cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'],
    env: {...process.env, GIT_CONFIG_NOSYSTEM: '1', GIT_CONFIG_GLOBAL: '/dev/null',
      GIT_AUTHOR_NAME: 'Gate fixture', GIT_AUTHOR_EMAIL: 'fixture@example.invalid',
      GIT_COMMITTER_NAME: 'Gate fixture', GIT_COMMITTER_EMAIL: 'fixture@example.invalid'},
  }).trim()
  try {
    const root = join(base, 'source'), vendor = join(base, 'vendor-source'), input = join(base, 'input')
    const commitMessage = join(base, 'commit-message.txt')
    writeFileSync(commitMessage, 'test: full gate fixture\n')
    mkdirSync(root); mkdirSync(vendor)
    git(vendor, 'init', '-q')
    writeFileSync(join(vendor, 'retained.c'), 'vendor source\n')
    git(vendor, 'add', '.'); git(vendor, '-c', 'core.hooksPath=/dev/null', 'commit', '-q', '-F', commitMessage)
    const vendorCommit = git(vendor, 'rev-parse', 'HEAD')
    git(root, 'init', '-q')
    mkdirSync(join(root, 'scripts/release-ci'), {recursive: true}); mkdirSync(join(root, 'supercomputer'))
    for (const name of ['full-gate-contract.ts', 'known-failures.ts']) copyFileSync(join(import.meta.dir, name), join(root, 'scripts/release-ci', name))
    writeFileSync(join(root, 'scripts/release-ci/known-failures.json'), JSON.stringify({schema: 'gdp-known-failures/v1', baselineCommit: 'a'.repeat(40), evidence: {triageSha256: 'b'.repeat(64), comparisonSha256: 'c'.repeat(64)}, entries: [], requiredPass: ['exists']}))
    writeFileSync(join(root, '.gitignore'), 'node_modules\n')
    writeFileSync(join(root, 'package.json'), JSON.stringify({name: 'full-gate-fixture', version: '0.0.0', private: true}))
    writeFileSync(join(root, 'retained.c'), 'root source\n')
    writeFileSync(join(root, 'verify.ts'), `import {readFileSync} from 'node:fs'\nif(readFileSync('retained.c','utf8')!=='root source\\n'||readFileSync('vendor/pinned/retained.c','utf8')!=='vendor source\\n')throw Error('source missing or changed');console.log('canonical-source-ok')\n`)
    writeFileSync(join(root, 'supercomputer/suite.json'), JSON.stringify([{name: 'roundtrip', cmd: 'bun verify.ts', cwd: '.', timeout: 30}, {name: 'exists', cmd: 'true', cwd: '.', timeout: 30}]))
    git(root, '-c', 'protocol.file.allow=always', 'submodule', 'add', '-q', vendor, 'vendor/pinned')
    git(root, 'add', '.'); git(root, '-c', 'core.hooksPath=/dev/null', 'commit', '-q', '-F', commitMessage)
    await prepare(root, input)
    const manifestBytes = readFileSync(join(input, 'manifest.json'))
    const manifest = JSON.parse(manifestBytes.toString('utf8'))
    const output = join(base, 'output'); mkdirSync(output)
    process.env.SUPERCOMPUTER_OUTPUT_DIR = output
    expect(await worker(input, digest(manifestBytes), 'roundtrip')).toBe(0)
    const provisioned = JSON.parse(readFileSync(join(output, 'PROVISIONED.json'), 'utf8'))
    expect(provisioned.commit).toBe(git(root, 'rev-parse', 'HEAD'))
    expect(provisioned.vendorPins).toEqual({'vendor/pinned': vendorCommit})
    expect(readFileSync(join(output, 'stdout.log'), 'utf8')).toContain('canonical-source-ok')
    expect(JSON.parse(readFileSync(join(output, 'LEAN-DIAGNOSTICS.json'), 'utf8'))).toEqual({schema: 'gdp-lean-diagnostics/v1', logs: []})

    const second = join(base, 'tampered-output'); mkdirSync(second)
    process.env.SUPERCOMPUTER_OUTPUT_DIR = second
    const archive = join(input, manifest.repositories[1].archive)
    const corrupt = Buffer.from(readFileSync(archive)); corrupt[512] = (corrupt[512] ?? 0) ^ 1
    writeFileSync(archive, corrupt)
    await refuses(worker(input, digest(manifestBytes), 'roundtrip'), 'archive mismatch')
    await refuses(worker(input, '0'.repeat(64), 'roundtrip'), 'manifest hash mismatch')
    await refuses(worker(input, digest(manifestBytes), 'omitted'), 'invalid manifest')
  } finally {
    if (previousOutput === undefined) delete process.env.SUPERCOMPUTER_OUTPUT_DIR
    else process.env.SUPERCOMPUTER_OUTPUT_DIR = previousOutput
    rmSync(base, {recursive: true, force: true})
  }
}, 90_000)
