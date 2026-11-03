// Opt-in, owned-only execution probe. Not registered in the quick suite: it installs a local tarball.
import {spawnSync, type SpawnSyncReturns} from 'node:child_process'
import {cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, realpathSync, rmSync, writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {tmpdir} from 'node:os'
import {basename, dirname, isAbsolute, join, resolve} from 'node:path'
import {pathToFileURL} from 'node:url'
import {stripVTControlCharacters} from 'node:util'

type Law = {name: string, expr: string, verdict: string, run?: string[], review?: string}
type Result = {exit: number, rules: {file: string, entry: string, ok: boolean, checked?: string, laws: Law[], security?: Law[]}[]}
type Pins = {base: string, tree: string, files: Record<string, string>}
type Action = {inputs: {security: {default: string}}, runs: {steps: {if?: string, run?: string}[]}}
const root = resolve(import.meta.dir, '../..')
const argument = (name: string) => { const at = process.argv.indexOf(name); if (at < 0 || !process.argv[at + 1]) throw Error(`required ${name}`); return resolve(process.argv[at + 1]!) }
const out = argument('--out'), packFile = argument('--pack')
if (existsSync(join(out, 'summary.json'))) throw Error('refuse to overwrite a prior receipt')
mkdirSync(out, {recursive: true})
const work = mkdtempSync(join(tmpdir(), 'gdp-owned-package-'))
const pins = JSON.parse(readFileSync(join(import.meta.dir, 'packaged-source-pins.json'), 'utf8')) as Pins
const sha = (file: string) => createHash('sha256').update(readFileSync(file)).digest('hex')
function requireThat(ok: unknown, message: string): asserts ok { if (!ok) throw Error(message) }
const env: NodeJS.ProcessEnv & {NPM_CONFIG_CACHE: string} = {...process.env, NPM_CONFIG_CACHE: join(work, 'install-cache')}
const commands: Record<string, unknown>[] = [], outcomes: Record<string, unknown>[] = [], failures: string[] = [], gaps: string[] = []
const layers: Record<string, unknown> = {}
let finished = false, artifactPath: string | undefined
const save = () => writeFileSync(join(out, 'summary.json'), JSON.stringify({scope: 'owned local package/entrypoint probe; not GitHub runner or released-package evidence', base: pins.base, tree: pins.tree, finished, complete: finished && failures.length === 0 && gaps.length === 0, failures, gaps, layers, outcomes, commands}, null, 2) + '\n')
function run(id: string, exe: string, args: string[], cwd = work, timeout = 90_000, childEnv = env): SpawnSyncReturns<string> {
  const result = spawnSync(exe, args, {cwd, env: childEnv, encoding: 'utf8', timeout, maxBuffer: 16 << 20})
  writeFileSync(join(out, id + '.stdout'), result.stdout ?? '')
  writeFileSync(join(out, id + '.stderr'), result.stderr ?? '')
  commands.push({id, exe, args, cwd, timeout, status: result.status, signal: result.signal, error: result.error?.message ?? null})
  save()
  return result
}
const status = (r: SpawnSyncReturns<string>, wanted: number, what: string) => requireThat(r.status === wanted && r.signal === null && !r.error, `${what}: status ${r.status}, signal ${r.signal}, ${r.error?.message ?? ''}`)
function attempt<T>(name: string, body: () => T): T | undefined {
  try { const value = body(); outcomes.push({name, status: 'pass'}); save(); return value }
  catch (error) { const message = `${name}: ${(error as Error).message}`; failures.push(message); outcomes.push({name, status: 'fail', message}); save(); return undefined }
}
const replaceOnce = (text: string, before: string, after: string) => { requireThat(text.split(before).length === 2, 'nonunique fixture import'); return text.replace(before, after) }
function treeFiles(dir: string): string[] {
  return readdirSync(dir, {withFileTypes: true}).filter(e => e.name !== 'node_modules').flatMap(e => e.isDirectory() ? treeFiles(join(dir, e.name)).map(f => `${e.name}/${f}`) : [e.name]).sort()
}
try {
  cpSync(import.meta.filename, join(out, 'probe-source.ts'))
  cpSync(join(import.meta.dir, 'packaged-source-pins.json'), join(out, 'source-pins.json'))
  for (const [file, expected] of Object.entries(pins.files)) requireThat(sha(join(root, file)) === expected, `baseline source changed: ${file}`)
  layers.sourcePins = pins
  let node = realpathSync('/usr/bin/node')
  const initial = run('node-initial', node, ['--version'])
  status(initial, 0, 'initial node')
  if (!initial.stdout.startsWith('v22.')) {
    const toolchain = join(work, 'toolchain'); mkdirSync(toolchain)
    const install = run('node22-install', 'npm', ['install', '--prefix', toolchain, '--no-audit', '--no-fund', 'node@22.14.0'], work, 120_000)
    if (install.status === 0 && !install.error) node = join(toolchain, 'node_modules/node/bin/node')
    else gaps.push('Node22 install unavailable; local Action Node22 contract not exercised')
  }
  const version = run('node-selected', node, ['--version']); status(version, 0, 'selected node')
  env.PATH = `${dirname(node)}:${process.env.PATH ?? ''}`
  layers.runtime = {node: version.stdout.trim(), nodePath: node, bun: Bun.version, bunNodeCompatibility: process.version, localActionNode22: version.stdout.startsWith('v22.')}

  const packed = JSON.parse(readFileSync(packFile, 'utf8')) as {filename: string, integrity: string, files: {path: string}[]}[]
  requireThat(packed.length === 1 && basename(packed[0]!.filename) === packed[0]!.filename, 'one owned tarball required')
  const tarball = join(dirname(packFile), packed[0]!.filename), tarHash = sha(tarball)
  artifactPath = tarball
  const unpack = join(work, 'unpack'); mkdirSync(unpack)
  status(run('unpack', 'tar', ['-xzf', tarball, '-C', unpack]), 0, 'unpack')
  const files = packed[0]!.files.map(x => x.path).sort()
  requireThat(files.every(f => !isAbsolute(f) && !f.split('/').includes('..')), 'invalid owned package path')
  const manifest = Object.fromEntries(files.map(f => [f, sha(join(unpack, 'package', f))]))
  writeFileSync(join(out, 'artifact-files.json'), JSON.stringify(manifest, null, 2) + '\n')
  function verifyPackage(dir: string) {
    requireThat(JSON.stringify(treeFiles(dir)) === JSON.stringify(files), 'installed file inventory differs')
    for (const [file, digest] of Object.entries(manifest)) requireThat(sha(join(dir, file)) === digest, `installed bytes differ: ${file}`)
    return {path: realpathSync(dir), files: files.length, cliSha256: sha(join(dir, 'dist/core/cli.js'))}
  }
  const consumer = join(work, 'consumer'); mkdirSync(consumer)
  writeFileSync(join(consumer, 'package.json'), '{"name":"owned-security-consumer","private":true,"type":"module"}\n')
  status(run('consumer-install', 'npm', ['install', '--no-audit', '--no-fund', tarball, 'typescript@5.9.3', '@gdp-ts/core@0.1.0'], consumer, 120_000), 0, 'consumer install')
  const installed = join(consumer, 'node_modules/gdp-wired'), cli = join(installed, 'dist/core/cli.js')
  layers.artifact = {tarball, sha256: tarHash, integrity: packed[0]!.integrity, installed: verifyPackage(installed)}

  const nativeDir = join(consumer, 'native'); mkdirSync(nativeDir)
  const captured = join(work, 'captured'); mkdirSync(captured)
  const sourceTest = readFileSync(join(root, 'research/security/call-order.test.ts'), 'utf8')
  let copy = replaceOnce(sourceTest, "from '../../core/cli.ts'", "from './adapter.ts'")
  copy = replaceOnce(copy, "from './score.ts'", `from ${JSON.stringify(pathToFileURL(join(root, 'research/security/score.ts')).href)}`)
  writeFileSync(join(nativeDir, 'call-order.test.ts'), copy)
  const adapter = `import {check as packagedCheck} from ${JSON.stringify(pathToFileURL(cli).href)}\n` +
    `import {readFileSync,writeFileSync,mkdirSync,copyFileSync} from 'node:fs'\nimport {dirname,basename,join} from 'node:path'\nimport {createHash} from 'node:crypto'\n` +
    `export const check: typeof packagedCheck = async (targets, options, each) => {\n` +
    ` const rows = targets.map(file => {const version=basename(dirname(file)); if(basename(file)!=='OwnedOrder.java'||!['original','repaired'].includes(version)) throw Error('unexpected owned target'); const dir=join(${JSON.stringify(captured)},version);mkdirSync(dir,{recursive:true});copyFileSync(file,join(dir,'OwnedOrder.java'));copyFileSync(join(dirname(file),'ReplayOrder.java'),join(dir,'ReplayOrder.java'));return {file,version,sha256:createHash('sha256').update(readFileSync(file)).digest('hex')};});\n` +
    ` const result=await packagedCheck(targets,options,each);\n` +
    ` writeFileSync(join(${JSON.stringify(out)},'library-'+rows[0]!.version+'.json'),JSON.stringify({module:${JSON.stringify(pathToFileURL(cli).href)},options,rows,result},null,2));return result;\n}\n`
  writeFileSync(join(nativeDir, 'adapter.ts'), adapter)
  writeFileSync(join(out, 'native-test-copy.ts'), copy)
  writeFileSync(join(out, 'native-adapter.ts'), adapter)
  const suite = run('native-suite', process.execPath, ['test', join(nativeDir, 'call-order.test.ts')], consumer, 180_000)
  const suiteText = stripVTControlCharacters(suite.stdout + suite.stderr)
  const nativeNames = ['owned multi-call witness order changes the native policy outcome', 'owned native process failures never produce an accepted result row', 'owned invalid traces do not launch the armed native entry probe']
  const nativePassed = nativeNames.every(n => suiteText.includes('(pass) ' + n))
  const suiteRecord = {status: suite.status, passed: Number(/\b(\d+) pass\b/.exec(suiteText)?.[1] ?? 0), failures: Number(/\b(\d+) fail\b/.exec(suiteText)?.[1] ?? 0), skipped: Number(/\b(\d+) skip\b/.exec(suiteText)?.[1] ?? 0), nativePassed,
    originalTestSha256: sha(join(root, 'research/security/call-order.test.ts')), copiedTestSha256: sha(join(nativeDir, 'call-order.test.ts')), importChangesOnly: 2, packagedModule: cli}
  layers.nativeLibrarySuite = suiteRecord
  if (!nativePassed || suiteRecord.skipped) {
    gaps.push('native regression execution incomplete; retain skip/failure evidence')
    outcomes.push({name: 'installed-library native regressions', status: 'gap'})
    if (suite.status !== 0) failures.push('native suite failed; inspect retained log')
  } else attempt('installed-library native regressions', () => { status(suite, 0, 'native suite'); requireThat(suiteRecord.passed === 7 && suiteRecord.failures === 0, 'not all seven native/unit controls passed') })
  cpSync(captured, join(out, 'sources'), {recursive: true})
  const fixtureHash = (versionName: string): string => {
    const receipt = JSON.parse(readFileSync(join(out, 'library-' + versionName + '.json'), 'utf8')) as {module: string, rows: {version: string, sha256: string}[]}
    requireThat(receipt.module === pathToFileURL(cli).href && receipt.rows.length === 1 && receipt.rows[0]!.version === versionName, 'captured fixture association changed')
    return receipt.rows[0]!.sha256
  }

  const actionRoot = join(work, 'action'); mkdirSync(actionRoot)
  status(run('fixture-git-init', 'git', ['init', '-q'], actionRoot), 0, 'fixture git init')
  for (const name of ['candidate.ts', 'stated-broken.ts']) {
    const source = join(root, '.github/fixtures/security-action', name)
    cpSync(source, join(actionRoot, name)); cpSync(source, join(out, 'sources', name))
  }
  const action = Bun.YAML.parse(readFileSync(join(root, 'action.yml'), 'utf8')) as Action
  requireThat(action.inputs.security.default === 'false', 'Action default changed')
  const actionEnv = {...env, NPM_CONFIG_CACHE: join(work, 'action-cache')}
  const cliRows: Record<string, Result> = {}, actionRows: Record<string, Result> = {}
  let launches = 0
  function executeCase(kind: 'cli' | 'action', name: string, file: string, expectedHash: string, security: boolean, java = false): Result {
    requireThat(sha(file) === expectedHash, 'fixture source mismatch before launch')
    const args = ['--entry', java ? 'OwnedOrder' : 'Counter', ...(java ? ['--methods', 'arm,hit'] : []), '--no-propose', '--ms', java ? '3000' : '2000', '--json']
    launches++
    let result: SpawnSyncReturns<string>
    if (kind === 'cli') result = run(name, node, [cli, 'check', file, ...args, ...(security ? ['--security'] : [])], consumer)
    else {
      requireThat(version.stdout.startsWith('v22.'), 'Action Node22 unavailable')
      const condition = security ? "inputs.security == 'true'" : "inputs.security != 'true'"
      const steps = action.runs.steps.filter(s => s.if === condition && s.run)
      requireThat(steps.length === 1, 'unique fixed Action run step required')
      const substitutions = {version: 'file:' + tarball, paths: file, args: args.join(' ')}
      requireThat(/^[a-zA-Z0-9_./:-]+$/.test(substitutions.version) && /^[a-zA-Z0-9_./-]+$/.test(file), 'owned shell substitution is not simple')
      let command = steps[0]!.run!
      for (const [key, value] of Object.entries(substitutions)) command = replaceOnce(command, '${{ inputs.' + key + ' }}', value)
      result = run(name, 'bash', ['-c', command], actionRoot, 90_000, actionEnv)
    }
    requireThat(!result.error && result.signal === null, 'CLI process did not finish normally')
    const json = JSON.parse(result.stdout) as Result
    requireThat(result.status === json.exit && Array.isArray(json.rules) && json.rules.length === 1, 'invalid CLI receipt')
    requireThat(sha(file) === expectedHash, 'fixture source changed after execution')
    const rule = json.rules[0]!
    requireThat(resolve(kind === 'cli' ? consumer : actionRoot, rule.file) === file && rule.entry === (java ? 'OwnedOrder' : 'Counter') && rule.ok, 'CLI source/entry association mismatch')
    requireThat(!java || !!rule.checked, 'native reader execution evidence missing')
    requireThat(security ? Array.isArray(rule.security) && rule.security.every(l => l.review === 'required') : rule.security === undefined, 'opt-in candidate separation failed')
    outcomes.push({name, status: 'observed', kind, security, source: file, sourceSha256: expectedHash, exit: json.exit, candidateCount: rule.security?.length ?? 0})
    return json
  }
  for (const kind of ['cli', 'action'] as const) {
    if (kind === 'action' && !version.stdout.startsWith('v22.')) { gaps.push('local Action run steps not executed under required Node22'); continue }
    for (const security of [false, true]) for (const fileName of ['candidate.ts', 'stated-broken.ts']) {
      const name = `${kind}-${security ? 'on' : 'off'}-${fileName.slice(0, -3)}`
      attempt(name, () => {
        const file = join(actionRoot, fileName), result = executeCase(kind, name, file, pins.files['.github/fixtures/security-action/' + fileName]!, security)
        requireThat(result.exit === (fileName === 'candidate.ts' ? 0 : 1), 'unexpected stated-law exit')
        if (fileName === 'candidate.ts' && security) requireThat(result.rules[0]!.security!.some(l => l.verdict === 'broken'), 'expected review-required broken candidate missing')
        if (fileName === 'stated-broken.ts') requireThat(result.rules[0]!.laws.some(l => l.verdict === 'broken'), 'broken stated law missing')
      })
    }
    if (!nativePassed) { gaps.push(kind + ' Java fixture path not claimed without native preconditions'); continue }
    for (const security of [false, true]) for (const versionName of ['original', 'repaired']) {
      const name = `${kind}-${security ? 'on' : 'off'}-${versionName}`
      const value = attempt(name, () => {
        const file = join(captured, versionName, 'OwnedOrder.java')
        const expected = fixtureHash(versionName)
        const result = executeCase(kind, name, file, expected, security, true)
        requireThat(result.exit === (versionName === 'original' ? 1 : 0), 'native fixture CLI exit changed')
        requireThat(result.rules[0]!.laws.length === 1 && result.rules[0]!.laws[0]!.name === 'no value writes' && result.rules[0]!.laws[0]!.expr === 'value == old(value)', 'original policy identity changed')
        requireThat(result.rules[0]!.laws[0]!.verdict === (versionName === 'original' ? 'broken' : 'proven'), 'native fixture policy verdict changed')
        return result
      })
      if (value) (kind === 'cli' ? cliRows : actionRows)[`${security}-${versionName}`] = value
    }
    const rows = kind === 'cli' ? cliRows : actionRows
    for (const security of [false, true]) attempt(`${kind}-${security}-native-witness`, () => {
      const trace = rows[`${security}-original`]?.rules[0]?.laws[0]?.run
      requireThat(Array.isArray(trace) && trace.length > 0 && trace.every(c => c === 'arm()' || c === 'hit()'), 'exact allowlisted CLI witness missing')
      const exact = trace.map(c => c === 'arm()' ? 'arm' : 'hit')
      const reordered = [...exact.filter(c => c === 'hit'), ...exact.filter(c => c === 'arm')]
      requireThat(JSON.stringify(exact) !== JSON.stringify(reordered), 'order contrast is not distinct')
      const controls: Record<string, unknown>[] = []
      for (const versionName of ['original', 'repaired']) {
        const dir = join(captured, versionName), file = join(dir, 'OwnedOrder.java'), before = sha(file)
        requireThat(before === fixtureHash(versionName), 'native source differs from captured fixture')
        const driver = join(dir, 'ReplayOrder.java'), driverSha256 = sha(driver)
        status(run(`${kind}-${security}-${versionName}-compile`, 'javac', [file, driver], work, 30_000), 0, 'owned Java compile')
        for (const [order, calls] of [['exact', exact], ['reordered', reordered]] as const) {
          const r = run(`${kind}-${security}-${versionName}-${order}-native`, 'java', ['-cp', dir, 'ReplayOrder', ...calls], work, 10_000)
          status(r, 0, 'owned Java replay')
          const match = /^(true|false):(0|[1-9]\d*):(0|[1-9]\d*):(true|false)\n$/.exec(r.stdout)
          requireThat(match && match[0] === r.stdout && Number.isSafeInteger(Number(match[2])) && Number.isSafeInteger(Number(match[3])) && Number(match[3]) === calls.length && match[4] === 'true', 'invalid native row')
          const expected = versionName === 'original' && order === 'exact'
          requireThat((match[1] === 'true') === expected && (Number(match[2]) > 0) === expected, 'native policy contrast changed')
          requireThat(sha(file) === before && sha(driver) === driverSha256, 'native source or driver changed')
          controls.push({version: versionName, order, calls, stdout: r.stdout, sourceSha256: before, driverSha256,
            entry: 'OwnedOrder', constructor: '()', constructorArguments: [], policy: rows[`${security}-${versionName}`]!.rules[0]!.laws[0]})
        }
      }
      layers[`${kind}-${security}-native`] = {witness: trace, controls}
    })
  }
  const beforeMismatch = launches
  attempt('source mismatch rejected before launch', () => {
    let rejected = false
    try { executeCase('cli', 'must-not-launch', join(actionRoot, 'candidate.ts'), '0'.repeat(64), false) } catch { rejected = true }
    requireThat(rejected && launches === beforeMismatch, 'source mismatch launched a CLI')
  })
  if (version.stdout.startsWith('v22.')) attempt('local Action cache equals packed artifact', () => {
    const cache = join(actionEnv.NPM_CONFIG_CACHE, '_npx')
    const dirs = existsSync(cache) ? readdirSync(cache).map(k => join(cache, k, 'node_modules/gdp-wired')).filter(existsSync) : []
    requireThat(dirs.length > 0, 'no installed Action artifact located; association unestablished')
    layers.localAction = {kind: 'actual run-step shell/npx execution, not GitHub composite orchestration', installedPackages: dirs.map(verifyPackage)}
  })
  verifyPackage(installed)
  requireThat(sha(tarball) === tarHash, 'tarball bytes changed')
  for (const [file, expected] of Object.entries(pins.files)) requireThat(sha(join(root, file)) === expected, `baseline source changed after probes: ${file}`)
} catch (error) { failures.push('setup/probe: ' + (error as Error).message) }
finally {
  finished = true; save()
  if (process.argv.includes('--emit-packet')) {
    const packet = join(work, 'packet.tgz')
    const args = ['-czf', packet, '-C', dirname(out), basename(out)]
    if (artifactPath) args.push('-C', dirname(artifactPath), basename(artifactPath), basename(packFile))
    const archived = spawnSync('tar', args, {encoding: 'utf8', timeout: 30_000})
    if (archived.status === 0 && !archived.error) {
      const bytes = readFileSync(packet)
      console.log(`OWNED_PACKAGE_PACKET_BEGIN ${sha(packet)} ${bytes.length}`)
      console.log(bytes.toString('base64').match(/.{1,76}/g)!.join('\n'))
      console.log('OWNED_PACKAGE_PACKET_END')
    } else { failures.push('packet export failed: ' + (archived.stderr ?? archived.error?.message ?? 'unknown')); save() }
  }
  rmSync(work, {recursive: true, force: true})
}
console.log(JSON.stringify({complete: failures.length === 0 && gaps.length === 0, failures, gaps, summary: join(out, 'summary.json')}))
process.exitCode = failures.length ? 1 : gaps.length ? 2 : 0
