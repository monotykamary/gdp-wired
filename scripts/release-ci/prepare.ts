// Local metadata preparation only: no installs, tests, worker launch, controller or credential access.
import {execFileSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {copyFileSync, existsSync, mkdirSync, readFileSync, readdirSync, statSync, writeFileSync} from 'node:fs'
import {join, resolve, sep} from 'node:path'

const BASE = 'b11e1f651618b3d3fcaf6cec66b4a8b0203cdcd3'
const CANDIDATE = 'c8411149d2c6c3c060a0665a79f10523b1281cbc'
const repo = resolve(import.meta.dir, '../..')
const [outArg, controlArg, releaseArg, restoredArg = '/tmp'] = process.argv.slice(2)
if (!outArg || !controlArg) throw Error('usage: bun scripts/release-ci/prepare.ts INPUT_DIR CONTROL_DIR [FULL_RELEASE_SHA] [RESTORED_DIR]')
const out = resolve(outArg), control = resolve(controlArg), restored = resolve(restoredArg)
const git = (...args: string[]): Buffer => execFileSync('git', args, {cwd: repo, maxBuffer: 128 * 1024 * 1024})
const text = (...args: string[]): string => git(...args).toString('utf8').trim()
const release = releaseArg ?? text('rev-parse', 'HEAD')
if (!/^[a-f0-9]{40}$/.test(release)) throw Error('release snapshot must be a full commit SHA')
const within = (path: string, parent: string): boolean => path === parent || path.startsWith(parent + sep)
if (out === '/' || control === '/' || within(out, repo) || within(control, repo) || within(out, control) || within(control, out)) {
  throw Error('input and control directories must be separate, outside the source checkout')
}
for (const dir of [out, control]) {
  if (existsSync(dir) && (!statSync(dir).isDirectory() || readdirSync(dir).length)) throw Error(`refusing nonempty output: ${dir}`)
}
for (const sha of [BASE, CANDIDATE, release]) if (text('rev-parse', `${sha}^{commit}`) !== sha) throw Error('commit identity mismatch')
const sourceMeta = join(restored, 'gdp-c841-supplement-meta')
if (readFileSync(join(sourceMeta, 'main.sha'), 'utf8').trim() !== CANDIDATE) throw Error('restored metadata is not the frozen candidate')
const roles = ['gdp-ts', 'handwired'] as const
const sourceArchives = join(restored, 'gdp-ci-fix-optional/archives')
const digest = (path: string): string => createHash('sha256').update(readFileSync(path)).digest('hex')
const vendor: Record<string, {sha: string, tree: string, archive: string, sha256: string}> = {}
for (const role of roles) {
  const sha = readFileSync(join(sourceMeta, `${role}.sha`), 'utf8').trim()
  const tree = readFileSync(join(sourceMeta, `${role}.tree`), 'utf8').trim()
  const commit = join(sourceMeta, `${role}.commit`)
  if (text('hash-object', '-t', 'commit', commit) !== sha || !readFileSync(commit, 'utf8').startsWith(`tree ${tree}\n`)) throw Error(`restored vendor metadata mismatch: ${role}`)
  for (const ref of [BASE, CANDIDATE, release]) {
    const row = text('ls-tree', ref, `vendor/${role}`)
    if (row !== `160000 commit ${sha}\tvendor/${role}`) throw Error(`vendor changed outside the restored archives: ${role} at ${ref}`)
  }
  const archive = join(sourceArchives, `${role}.tar`)
  if (!statSync(archive).isFile()) throw Error(`missing vendor archive: ${role}`)
  vendor[role] = {sha, tree, archive, sha256: digest(archive)}
}
const pkg = JSON.parse(git('show', `${release}:package.json`).toString()) as {version: string}
const cli = JSON.parse(git('show', `${release}:packages/cli/package.json`).toString()) as {version: string, dependencies: Record<string, string>}
if (pkg.version !== '0.48.0' || cli.version !== pkg.version || cli.dependencies['gdp-wired'] !== pkg.version) throw Error('release snapshot versions are not aligned at 0.48.0')
const smoke = git('show', `${release}:scripts/smoke.sh`).toString()
if (!smoke.includes('unchecked Python laws exit 2') || !smoke.includes('check wallet.ts --no-propose --cert certs')) throw Error('release snapshot lacks the prepared smoke repair')
const expectedReceipts: Array<[string, string]> = [
  ['runs/c841-supplement-resume4-20261110/summary.tsv', '79f3ab33576ff47997a195f11a5055df22e93d20e222241b35fb0055780189cd'],
  ['runs/c841-supplement-resume4-20261110/placement.json', '7eb18f1be78c8d575b25a4023629abd8e5089129271e6fa1f5430af1c152cbdf'],
  ['runs/c841-supplement-resume4-20261110/backends.json', '5b3696b01360a434109020cae5ce57e792528027d52b2cbb7de25c7f984bfaa7'],
  ['runs/c841-package-smoke-resume4-20261110/exact-candidate-package-consumer-smoke.log', '06f9dbdc83d5de047c276e33e5b9fb4cff9b1ba54814485816aedd8fcef0be68'],
  ['runs/c841-privacy-resume4-20261110/release-boundary-privacy.log', '3297d0e00d365b4a5e7e84b9c55973ff65096d8a8fb626d8a2dce7e3ffcc97be'],
  ['runs/c841-privacy-summary-resume4-20261110/privacy-summary.recovered.log', '1e1b025fddd2b7d49f63f3c0bb1a43367e1c92c8d6ad4b883cd4cdfe6668c2aa'],
]
for (const [path, expected] of expectedReceipts) if (digest(join(repo, path)) !== expected) throw Error(`retained receipt changed: ${path}`)
mkdirSync(out, {recursive: true}); mkdirSync(control, {recursive: true})
mkdirSync(join(out, 'base-archive'))
git('archive', '--format=tar', `--output=${join(out, 'base-archive/base.tar')}`, BASE)
const metadata = (name: string, sha: string): void => {
  const dir = join(out, name)
  mkdirSync(dir)
  writeFileSync(join(dir, 'main.sha'), sha + '\n')
  writeFileSync(join(dir, 'main.tree'), text('rev-parse', `${sha}^{tree}`) + '\n')
  writeFileSync(join(dir, 'main.commit'), git('cat-file', 'commit', sha))
  writeFileSync(join(dir, 'candidate.patch'), git('diff', '--no-ext-diff', '--no-textconv', '--no-color', '--binary', '--full-index', '--no-renames', '--src-prefix=a/', '--dst-prefix=b/', BASE, sha, '--'))
  if (text('hash-object', '-t', 'commit', join(dir, 'main.commit')) !== sha) throw Error('written root commit mismatch')
  for (const role of roles) for (const suffix of ['sha', 'tree', 'commit']) copyFileSync(join(sourceMeta, `${role}.${suffix}`), join(dir, `${role}.${suffix}`))
}
metadata('candidate-meta', CANDIDATE)
metadata('release-meta', release)
const files = ['setup-b11.sh', 'e0-verify.ts', 'verify-negative-controls.ts', 'current-verify.sh', 'package-smoke.sh', 'package-smoke-node.sh', 'hooks.py']
for (const file of files) copyFileSync(join(import.meta.dir, file), join(control, file))
const config = readFileSync(join(repo, 'supercomputer.toml'), 'utf8')
if (config.split('hooks = "supercomputer/hooks.py"').length !== 2) throw Error('unexpected source hooks setting')
writeFileSync(join(control, 'supercomputer.toml'), config.replace('hooks = "supercomputer/hooks.py"', 'hooks = "hooks.py"'))
writeFileSync(join(control, 'source-root.txt'), repo + '\n')
const jobs = (path: string, value: unknown): void => writeFileSync(join(out, path), JSON.stringify(value, null, 2) + '\n')
jobs('verify.jobs.json', [{name: 'verify-39-job-supplement', cmd: 'bash current-verify.sh', cpu: 2, memory: 8192, timeout: 900, vm_type: 'large'}])
jobs('package-smoke.jobs.json', [20, 24].map(major => ({name: `release-package-node-${major}`, cmd: `bash package-smoke.sh ${major}`, cpu: 2, memory: 8192, timeout: 900, vm_type: 'large'})))
const env = {...process.env, GIT_EDITOR: ':', EDITOR: ':', GIT_AUTHOR_NAME: 'CI lane', GIT_AUTHOR_EMAIL: 'ci@example.invalid', GIT_COMMITTER_NAME: 'CI lane', GIT_COMMITTER_EMAIL: 'ci@example.invalid'}
const controlGit = (...args: string[]): Buffer => execFileSync('git', args, {cwd: control, env})
controlGit('init', '-q')
controlGit('add', ...files, 'supercomputer.toml', 'source-root.txt')
const message = join(control, '.git/prepare-message.txt')
writeFileSync(message, 'chore(ci): prepare exact release worker controls\n')
controlGit('-c', 'core.hooksPath=/dev/null', 'commit', '-q', '-F', message)
const controlSha = controlGit('rev-parse', 'HEAD').toString().trim()
const manifest = {
  state: 'prepared-only', submitted: false, runtimeValidated: false,
  baseline: BASE, candidate: CANDIDATE, release, version: pkg.version, controlSha,
  baseArchiveSha256: digest(join(out, 'base-archive/base.tar')),
  vendor, controls: Object.fromEntries(files.map(file => [file, digest(join(control, file))])),
  retainedReceipts: Object.fromEntries(expectedReceipts),
  mounts: {baseArchive: join(out, 'base-archive'), candidateMeta: join(out, 'candidate-meta'), releaseMeta: join(out, 'release-meta'), sourceArchives, receipts: join(repo, 'runs/c841-supplement-resume4-20261110')},
}
jobs('restoration.json', manifest)
console.log('LOCAL_RELEASE_INPUTS_PREPARED ' + JSON.stringify({baseline: BASE, candidate: CANDIDATE, release, controlSha, submitted: false, runtimeValidated: false}))
