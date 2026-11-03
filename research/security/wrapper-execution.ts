// Explicit owned research only. The private consumer forces both packages to local tarballs.
import {spawnSync, type SpawnSyncReturns} from 'node:child_process'
import {createHash} from 'node:crypto'
import {cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, realpathSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {basename, dirname, isAbsolute, join, resolve} from 'node:path'

type Pins = {base: string, tree: string, files: Record<string, string>}
type Fixture = {text: string, sha256: string}
type Fixtures = {source: string, files: Record<'original' | 'repaired' | 'driver', Fixture>}
type Package = {name: string, version: string, bin: Record<string, string>, dependencies?: Record<string, string>}
type Law = {name: string, expr: string, verdict: string, review?: string, run?: string[]}
type Result = {exit: number, rules: {file: string, entry: string, checked?: string, ctor?: string, laws: Law[], security?: Law[], ok: boolean}[]}
const root = resolve(import.meta.dir, '../..')
function required(name: string) { const i = process.argv.indexOf(name); if (i < 0 || !process.argv[i + 1]) throw Error(`required ${name}`); return resolve(process.argv[i + 1]!) }
function demand(ok: unknown, why: string): asserts ok { if (!ok) throw Error(why) }
const out = required('--out'), corePack = required('--core-pack'), wrapperPack = required('--wrapper-pack')
demand(!existsSync(out), 'refuse to overwrite any prior output directory')
mkdirSync(out, {recursive: true})
const work = mkdtempSync(join(tmpdir(), 'gdp-owned-wrapper-'))
const hash = (file: string) => createHash('sha256').update(readFileSync(file)).digest('hex')
const hashText = (text: string) => createHash('sha256').update(text).digest('hex')
const pins = JSON.parse(readFileSync(join(import.meta.dir, 'wrapper-source-pins.json'), 'utf8')) as Pins
const fixtures = JSON.parse(readFileSync(join(import.meta.dir, 'wrapper-owned-fixtures.json'), 'utf8')) as Fixtures
const env: NodeJS.ProcessEnv & {NPM_CONFIG_CACHE: string} = {...process.env, NPM_CONFIG_CACHE: join(work, 'npm-cache')}
const commands: Record<string, unknown>[] = [], checks: Record<string, unknown>[] = [], failures: string[] = [], gaps: string[] = []
const data: Record<string, unknown> = {historicalLabels: {base: pins.base, tree: pins.tree}, pinScope: 'Only enumerated file hashes are checked; labels are not HEAD or whole-tree attestation.', unexercised: ['wrapper-alone registry resolution', 'released registry artifacts', 'Node20 and other toolchain/platform versions', 'GitHub Action/workflow execution']}
let finished = false, packet: {sha256: string, bytes: number} | undefined
const artifacts: {meta: string, tarball: string}[] = []
const save = () => writeFileSync(join(out, 'summary.json'), JSON.stringify({finished, complete: finished && failures.length === 0 && gaps.length === 0, failures, gaps, data, checks, commands}, null, 2) + '\n')
function run(id: string, command: string, args: string[], cwd = work, timeout = 90_000, childEnv = env): SpawnSyncReturns<string> {
  const result = spawnSync(command, args, {cwd, env: childEnv, encoding: 'utf8', timeout, maxBuffer: 16 << 20})
  writeFileSync(join(out, id + '.stdout'), result.stdout ?? ''); writeFileSync(join(out, id + '.stderr'), result.stderr ?? '')
  commands.push({id, command, args, cwd, timeout, status: result.status, signal: result.signal, error: result.error?.message ?? null}); save()
  return result
}
const status = (r: SpawnSyncReturns<string>, expected: number, label: string) => demand(r.status === expected && r.signal === null && !r.error, `${label}: status ${r.status}, signal ${r.signal}, error ${r.error?.message ?? ''}`)
function attempt<T>(label: string, action: () => T): T | undefined {
  try { const value = action(); checks.push({label, status: 'pass'}); save(); return value }
  catch (error) { const why = `${label}: ${(error as Error).message}`; failures.push(why); checks.push({label, status: 'fail', why}); save(); return undefined }
}
function inventory(dir: string): string[] { return readdirSync(dir, {withFileTypes: true}).filter(e => e.name !== 'node_modules').flatMap(e => e.isDirectory() ? inventory(join(dir, e.name)).map(f => `${e.name}/${f}`) : [e.name]).sort() }
try {
  cpSync(import.meta.filename, join(out, 'probe-source.ts'))
  cpSync(join(import.meta.dir, 'wrapper-source-pins.json'), join(out, 'source-pins.json'))
  cpSync(join(import.meta.dir, 'wrapper-owned-fixtures.json'), join(out, 'owned-fixtures.json'))
  for (const [file, expected] of Object.entries(pins.files)) demand(hash(join(root, file)) === expected, 'enumerated input changed: ' + file)
  data.checkedFiles = pins.files
  for (const fixture of Object.values(fixtures.files)) demand(hashText(fixture.text) === fixture.sha256, 'owned fixture bytes changed')
  let node = realpathSync('/usr/bin/node')
  const initial = run('node-initial', node, ['--version']); status(initial, 0, 'initial Node')
  if (!initial.stdout.startsWith('v22.')) {
    const dir = join(work, 'node22'); mkdirSync(dir)
    status(run('node22-install', 'npm', ['install', '--prefix', dir, '--no-audit', '--no-fund', 'node@22.14.0'], work, 120_000), 0, 'Node22 install')
    node = join(dir, 'node_modules/node/bin/node')
  }
  env.PATH = `${dirname(node)}:${process.env.PATH ?? ''}`
  const selected = run('node-selected', node, ['--version']); status(selected, 0, 'selected Node'); demand(selected.stdout.startsWith('v22.'), 'Node22 required')
  data.runtime = {node: selected.stdout.trim(), bun: Bun.version, bunNodeCompatibility: process.version}
  function packed(meta: string, expectedName: string) {
    const rows = JSON.parse(readFileSync(meta, 'utf8')) as {name: string, version: string, filename: string, integrity: string, files: {path: string}[]}[]
    demand(rows.length === 1 && rows[0]!.name === expectedName && basename(rows[0]!.filename) === rows[0]!.filename, 'unexpected packed artifact')
    const row = rows[0]!, tarball = join(dirname(meta), row.filename), dir = join(work, expectedName + '-unpack'); mkdirSync(dir)
    artifacts.push({meta, tarball}); status(run(expectedName + '-unpack', 'tar', ['-xzf', tarball, '-C', dir]), 0, 'unpack')
    const files = row.files.map(x => x.path).sort()
    demand(files.every(f => !isAbsolute(f) && !f.split('/').includes('..')), 'unexpected archive path')
    const manifest = Object.fromEntries(files.map(file => [file, hash(join(dir, 'package', file))]))
    const pkg = JSON.parse(readFileSync(join(dir, 'package/package.json'), 'utf8')) as Package
    writeFileSync(join(out, expectedName + '-files.json'), JSON.stringify(manifest, null, 2) + '\n')
    return {tarball, sha256: hash(tarball), integrity: row.integrity, files, manifest, pkg}
  }
  const core = packed(corePack, 'gdp-wired'), wrapper = packed(wrapperPack, 'gdp-wired-cli')
  demand(wrapper.pkg.dependencies?.['gdp-wired'] === core.pkg.version, 'wrapper dependency/core version mismatch')
  demand(wrapper.pkg.bin['gdp-wired-cli'] === 'bin.js' && core.pkg.bin['gdp-wired'] === 'dist/core/cli.js', 'unexpected package entrypoint')
  data.artifacts = {core: {sha256: core.sha256, integrity: core.integrity, version: core.pkg.version}, wrapper: {sha256: wrapper.sha256, integrity: wrapper.integrity, version: wrapper.pkg.version}}
  data.registryIndirection = {declared: wrapper.pkg.dependencies, exercised: 'Both packages explicitly installed from local file tarballs; private npm override forces all gdp-wired resolutions local. Wrapper-alone registry behavior is unexercised.'}
  const consumer = join(work, 'consumer'); mkdirSync(consumer)
  const consumerManifest = {name: 'owned-wrapper-probe', private: true, type: 'module', dependencies: {'gdp-wired': 'file:' + core.tarball, 'gdp-wired-cli': 'file:' + wrapper.tarball, typescript: '5.9.3', '@gdp-ts/core': '0.1.0'}, overrides: {'gdp-wired': '$gdp-wired'}}
  writeFileSync(join(consumer, 'package.json'), JSON.stringify(consumerManifest, null, 2))
  status(run('consumer-install', 'npm', ['install', '--no-audit', '--no-fund'], consumer, 120_000), 0, 'local co-install')
  cpSync(join(consumer, 'package.json'), join(out, 'consumer-package.json')); cpSync(join(consumer, 'package-lock.json'), join(out, 'consumer-package-lock.json'))
  const lock = JSON.parse(readFileSync(join(consumer, 'package-lock.json'), 'utf8')) as {packages: Record<string, {resolved?: string}>}
  const coreKeys = Object.keys(lock.packages).filter(k => k.endsWith('node_modules/gdp-wired'))
  demand(coreKeys.length === 1 && coreKeys[0] === 'node_modules/gdp-wired', 'unexpected core dependency layout')
  const coreResolution = lock.packages[coreKeys[0]!]!.resolved!
  demand(coreResolution.startsWith('file:') && resolve(consumer, coreResolution.slice(5)) === core.tarball, 'core resolved through registry rather than local tarball')
  data.lockCore = {key: coreKeys[0], resolved: coreResolution}
  const coreDir = join(consumer, 'node_modules/gdp-wired'), wrapperDir = join(consumer, 'node_modules/gdp-wired-cli')
  function verify(dir: string, expected: typeof core) {
    demand(JSON.stringify(inventory(dir)) === JSON.stringify(expected.files), 'installed package inventory differs')
    for (const [file, digest] of Object.entries(expected.manifest)) demand(hash(join(dir, file)) === digest, 'installed artifact mismatch: ' + file)
    return {path: realpathSync(dir), files: expected.files.length}
  }
  data.installed = {core: verify(coreDir, core), wrapper: verify(wrapperDir, wrapper)}
  const bin = join(wrapperDir, 'bin.js'), link = join(consumer, 'node_modules/.bin/gdp-wired-cli'), coreCli = realpathSync(join(coreDir, 'dist/core/cli.js'))
  demand(realpathSync(link) === realpathSync(bin), 'installed wrapper bin link differs')
  const resolver = "import {realpathSync} from 'node:fs'; import {fileURLToPath} from 'node:url'; console.log(JSON.stringify({core:realpathSync(fileURLToPath(import.meta.resolve('gdp-wired/cli'))),typescript:realpathSync(fileURLToPath(import.meta.resolve('typescript'))),node:process.version}))"
  const resolution = run('wrapper-import-resolution', node, ['--input-type=module', '-e', resolver], wrapperDir); status(resolution, 0, 'wrapper ESM resolution')
  const resolved = JSON.parse(resolution.stdout) as {core: string, typescript: string, node: string}
  demand(resolved.core === coreCli && resolved.node === selected.stdout.trim(), 'wrapper core/runtime resolution mismatch')
  data.entrypoint = {bin: realpathSync(bin), binSha256: hash(bin), coreCli, coreCliSha256: hash(coreCli), ...resolved}
  const offline = {...env, NPM_CONFIG_OFFLINE: 'true'}
  const lookup = run('npx-bin-resolution', 'npx', ['--no-install', '--call', 'command -v gdp-wired-cli'], consumer, 90_000, offline); status(lookup, 0, 'offline npx resolution')
  demand(realpathSync(lookup.stdout.trim()) === realpathSync(bin), 'npx did not select the installed wrapper')
  const java = run('java-version', 'java', ['-version'], work, 5000), javac = run('javac-version', 'javac', ['-version'], work, 5000)
  const native = java.status === 0 && !java.error && javac.status === 0 && !javac.error
  if (!native) gaps.push('Java toolchain unavailable: no Java CLI/native result claimed')
  const cases = join(work, 'fixtures'); mkdirSync(cases)
  for (const name of ['candidate', 'stated-broken']) cpSync(join(root, '.github/fixtures/security-action', name + '.ts'), join(cases, name + '.ts'))
  for (const name of ['original', 'repaired'] as const) { const dir = join(cases, name); mkdirSync(dir); writeFileSync(join(dir, 'OwnedOrder.java'), fixtures.files[name].text); writeFileSync(join(dir, 'ReplayOrder.java'), fixtures.files.driver.text) }
  cpSync(cases, join(out, 'sources'), {recursive: true})
  const results: Record<string, Result> = {}; let launches = 0
  function execute(label: string, file: string, digest: string, security: boolean, isJava: boolean) {
    demand(hash(file) === digest, 'fixture mismatch before launch'); demand(hash(bin) === wrapper.manifest['bin.js'], 'wrapper entrypoint changed')
    const args = ['--no-install', 'gdp-wired-cli', 'check', file, '--entry', isJava ? 'OwnedOrder' : 'Counter', ...(isJava ? ['--methods', 'arm,hit'] : []), '--no-propose', '--ms', isJava ? '3000' : '2000', '--json', ...(security ? ['--security'] : [])]
    launches++; const runResult = run(label, 'npx', args, consumer, 90_000, offline)
    demand(runResult.signal === null && !runResult.error, 'wrapper subprocess did not finish normally')
    const result = JSON.parse(runResult.stdout) as Result
    demand(result.exit === runResult.status && result.rules.length === 1, 'wrapper exit/JSON mismatch')
    const rule = result.rules[0]!
    demand(rule.ok && rule.entry === (isJava ? 'OwnedOrder' : 'Counter') && resolve(consumer, rule.file) === file, 'wrapper source/entry mismatch')
    demand(!isJava || !!rule.checked, 'Java reader execution marker absent')
    demand(security ? Array.isArray(rule.security) && rule.security.every(l => l.review === 'required') : rule.security === undefined, 'security opt-in separation failed')
    demand(hash(file) === digest, 'fixture bytes changed')
    checks.push({label, status: 'observed', sourceSha256: digest, exit: result.exit, security, candidates: rule.security?.length ?? 0})
    return result
  }
  for (const security of [false, true]) for (const name of ['candidate', 'stated-broken', 'original', 'repaired']) {
    const isJava = name === 'original' || name === 'repaired', label = `wrapper-${security ? 'on' : 'off'}-${name}`
    if (isJava && !native) { checks.push({label, status: 'gap'}); continue }
    const result = attempt(label, () => {
      const file = isJava ? join(cases, name, 'OwnedOrder.java') : join(cases, name + '.ts')
      const digest = isJava ? fixtures.files[name as 'original' | 'repaired'].sha256 : pins.files['.github/fixtures/security-action/' + name + '.ts']!
      const value = execute(label, file, digest, security, isJava), law = value.rules[0]!.laws[0]
      demand(value.exit === (name === 'candidate' || name === 'repaired' ? 0 : 1), 'unexpected stated-law exit')
      if (name === 'candidate' && security) demand(value.rules[0]!.security!.some(l => l.verdict === 'broken'), 'broken review candidate absent')
      if (name === 'stated-broken') demand(law?.verdict === 'broken', 'broken stated law absent')
      if (isJava) demand(law?.name === 'no value writes' && law.expr === 'value == old(value)' && law.verdict === (name === 'original' ? 'broken' : 'proven') && value.rules[0]!.ctor === undefined, 'owned Java policy/constructor mismatch')
      return value
    })
    if (result) results[`${security}-${name}`] = result
  }
  if (native) for (const security of [false, true]) attempt(`wrapper-${security}-native`, () => {
    const trace = results[`${security}-original`]?.rules[0]?.laws[0]?.run
    demand(Array.isArray(trace) && trace.length > 0 && trace.length <= 64 && trace.every(c => c === 'arm()' || c === 'hit()'), 'missing finite allowlisted wrapper witness')
    const exact = trace.map(c => c === 'arm()' ? 'arm' : 'hit'), reordered = [...exact.filter(c => c === 'hit'), ...exact.filter(c => c === 'arm')]
    demand(JSON.stringify(exact) !== JSON.stringify(reordered), 'order contrast absent')
    const controls: Record<string, unknown>[] = []
    for (const name of ['original', 'repaired'] as const) {
      const dir = join(cases, name), file = join(dir, 'OwnedOrder.java'), driver = join(dir, 'ReplayOrder.java')
      demand(hash(file) === fixtures.files[name].sha256 && hash(driver) === fixtures.files.driver.sha256, 'native source/driver changed before compile')
      status(run(`${security}-${name}-compile`, 'javac', [file, driver], work, 30_000), 0, 'owned fixture compile')
      for (const [order, calls] of [['exact', exact], ['reordered', reordered]] as const) {
        demand(hash(file) === fixtures.files[name].sha256 && hash(driver) === fixtures.files.driver.sha256, 'native source/driver changed before replay')
        const r = run(`${security}-${name}-${order}-native`, 'java', ['-cp', dir, 'ReplayOrder', ...calls], work, 10_000); status(r, 0, 'owned replay')
        const row = /^(true|false):(0|[1-9]\d*):(0|[1-9]\d*):(true|false)\n$/.exec(r.stdout)
        demand(row && row[0] === r.stdout && Number.isSafeInteger(Number(row[2])) && Number.isSafeInteger(Number(row[3])) && Number(row[3]) === calls.length && row[4] === 'true', 'invalid native row')
        const expected = name === 'original' ? calls.filter((c, i) => c === 'hit' && i > calls.indexOf('arm')).length : 0
        demand(Number(row[2]) === expected && (row[1] === 'true') === (expected > 0), 'native policy outcome differs')
        demand(hash(file) === fixtures.files[name].sha256 && hash(driver) === fixtures.files.driver.sha256, 'native source/driver changed after replay')
        controls.push({version: name, order, calls, stdout: r.stdout, sourceSha256: fixtures.files[name].sha256, driverSha256: fixtures.files.driver.sha256, entry: 'OwnedOrder', constructorArguments: [], policy: results[`${security}-${name}`]!.rules[0]!.laws[0]})
      }
    }
    data[`native-${security}`] = {trace, controls}
  })
  attempt('source mismatch rejected before wrapper launch', () => {
    const before = launches; let rejected = false
    try { execute('must-not-launch', join(cases, 'candidate.ts'), '0'.repeat(64), false, false) } catch { rejected = true }
    demand(rejected && launches === before, 'source mismatch launched wrapper')
  })
  verify(coreDir, core); verify(wrapperDir, wrapper)
  demand(hash(core.tarball) === core.sha256 && hash(wrapper.tarball) === wrapper.sha256, 'packed artifact bytes changed')
  for (const [file, expected] of Object.entries(pins.files)) demand(hash(join(root, file)) === expected, 'enumerated input changed after probes: ' + file)
} catch (error) { failures.push((error as Error).message) }
finally {
  finished = true; save()
  if (process.argv.includes('--emit-packet')) {
    const file = join(work, 'wrapper-packet.tgz'), args = ['-czf', file, '-C', dirname(out), basename(out)]
    for (const a of artifacts) args.push('-C', dirname(a.meta), basename(a.meta), basename(a.tarball))
    const archived = spawnSync('tar', args, {encoding: 'utf8', timeout: 30_000})
    if (archived.status === 0 && !archived.error) { const bytes = readFileSync(file); packet = {sha256: hash(file), bytes: bytes.length}; console.log(`WRAPPER_PACKET_BEGIN ${packet.sha256} ${packet.bytes}`); console.log(bytes.toString('base64').match(/.{1,76}/g)!.join('\n')); console.log(`WRAPPER_PACKET_END ${packet.sha256} ${packet.bytes}`) }
    else { failures.push('packet export failed'); save() }
  }
  rmSync(work, {recursive: true, force: true})
}
console.log(JSON.stringify({complete: failures.length === 0 && gaps.length === 0, failures, gaps, packet, summary: join(out, 'summary.json')}))
process.exitCode = failures.length ? 1 : gaps.length ? 2 : 0
