// Every front end as a user imports it: each one's subpath in package.json's exports, its types and its module built
// from a file the build compiles, the files it runs beside it copied by the build, and its function there. Imported
// through the package's own name where it is built (dist/), else from the source each export is built from.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {existsSync, readFileSync, readdirSync, statSync} from 'node:fs'

const root = new URL('../', import.meta.url).pathname
const pkg = JSON.parse(readFileSync(`${root}package.json`, 'utf8')) as {name: string, bin?: Record<string, string>, exports: Record<string, {types: string, default: string}>, files: string[]}
const build = JSON.parse(readFileSync(`${root}tsconfig.build.json`, 'utf8')) as {files: string[]}
// The front ends: the subpath, the function a user calls, and the files it runs beside its module (copied by the build).
const FRONT: [string, string, string[]][] = [
  ['./extract', 'extract', []], ['./extract', 'extractXState', []], ['./effect', 'extractEffect', []],
  ['./extract-py', 'extractPython', ['py/reader.py', 'py/harness.py']], ['./extract-rb', 'extractRuby', ['rb/reader.rb', 'rb/harness.rb']],
  ['./extract-ex', 'extractElixir', ['ex/reader.exs', 'ex/harness.exs', 'ex/json.exs']], ['./extract-rs', 'extractRust', ['rs/Cargo.toml', 'rs/src/main.rs']],
  ['./extract-c', 'extractC', []], ['./extract-cpp', 'extractCpp', []], ['./extract-java', 'extractJava', ['jvm/JavaReader.java', 'jvm/Harness.java']],
  ['./extract-kotlin', 'extractKotlin', ['jvm/KtReader.java']], ['./extract-go', 'extractGo', ['go/go.mod', 'go/reader.go']],
  ['./extract-swift', 'extractSwift', ['swift/Package.swift', 'swift/Sources/gdp-swiftreader/main.swift', 'swift/Harness.swift', 'swift/Main.swift']],
  ['./extract-sol', 'extractSolidity', ['sol/harness.py', 'sol/Replay.sol']],
]
const built = existsSync(`${root}dist/core/dsl.js`)
// The files a front end runs beside its module, as the build copies them (scripts/build.ts): every file under a
// directory of core/ but TypeScript, examples and build output.
const runtimeAssets = (): string[] => readdirSync(`${root}core`, {withFileTypes: true}).filter(d => d.isDirectory())
  .flatMap(d => readdirSync(`${root}core/${d.name}`, {recursive: true, encoding: 'utf8'}).map(f => `${d.name}/${f}`))
  .filter(f => !/(^|\/)(examples|generated|target|\.build|__pycache__|node_modules)(\/|$)|\.ts$|\.class$/.test(f) && statSync(`${root}core/${f}`).isFile())
// The assets the code names: asset('<dir>/<file>'), and each helper's (here('<file>') where here = f => asset(`<dir>/${f}`)).
const referenced = (): string[] => readdirSync(`${root}core`).filter(f => f.endsWith('.ts') && !f.endsWith('.test.ts')).flatMap(f => {
  const text = readFileSync(`${root}core/${f}`, 'utf8'), out = [...text.matchAll(/\basset\('([^']+)'\)/g)].map(m => m[1]!)
  for (const [, fn, dir] of text.matchAll(/const (\w+) = \(f: string\)(?:: string)? => [^\n]*asset\(`(\w+)\/\$\{f\}`\)/g)) out.push(...[...text.matchAll(new RegExp(`\\b${fn}\\('([^']+)'\\)`, 'g'))].map(m => `${dir}/${m[1]}`))
  return out
})

for (const [sub, fn, beside] of FRONT) {
  test(`${sub}: exported, typed, built and its ${fn} there, with proveRule`, async () => {
    const e = pkg.exports[sub]
    expect(e).toBeDefined()
    const src = e!.default.replace(/^\.\/dist\//, '').replace(/\.js$/, '.ts')
    expect(e!.types).toBe(e!.default.replace(/\.js$/, '.d.ts'))
    expect(build.files).toContain(src)
    for (const f of beside) {
      expect(existsSync(`${root}core/${f}`)).toBe(true)
      expect(runtimeAssets()).toContain(f)
      if (built) expect(existsSync(`${root}dist/core/${f}`)).toBe(true)
    }
    const mod = await import(built ? `${pkg.name}/${sub.slice(2)}` : `${root}${src}`) as Record<string, unknown>
    expect(typeof mod[fn]).toBe('function')
    // (one import: the rule read is proven from the same module)
    expect(typeof mod.proveRule).toBe('function')
  })
}

test('gdp-wired-cli: gdp-wired\'s CLI with TypeScript beside it, at gdp-wired\'s own version (they release together)', async () => {
  const cli = JSON.parse(readFileSync(`${root}packages/cli/package.json`, 'utf8')) as {name: string, version: string, bin: Record<string, string>, dependencies: Record<string, string>}
  expect(cli.name).toBe('gdp-wired-cli')
  expect(cli.version).toBe((pkg as unknown as {version: string}).version)
  expect(cli.dependencies['gdp-wired']).toBe(cli.version)
  expect(cli.dependencies.typescript).toBeDefined()
  expect(readFileSync(`${root}packages/cli/${cli.bin['gdp-wired-cli']}`, 'utf8')).toContain("from 'gdp-wired/cli'")
  const mod = await import(built ? `${pkg.name}/cli` : `${root}core/cli.ts`) as Record<string, unknown>
  expect(typeof mod.main).toBe('function')
})

test('the CLI is the package\'s bin, built from a file the build compiles', () => {
  expect(pkg.bin?.['gdp-wired']).toBe('dist/core/cli.js')
  expect(build.files).toContain('core/cli.ts')
  expect(readFileSync(`${root}core/cli.ts`, 'utf8').startsWith('#!/usr/bin/env node\n')).toBe(true)
  if (built) expect(readFileSync(`${root}dist/core/cli.js`, 'utf8').startsWith('#!/usr/bin/env node\n')).toBe(true)
})

test('the standalone checker is the package\'s second bin, and its reader and checker `gdp-wired/interchange`', async () => {
  expect(pkg.bin?.['gdp-wired-check']).toBe('dist/interchange/cli.js')
  expect(build.files).toContain('interchange/cli.ts')
  expect(readFileSync(`${root}interchange/cli.ts`, 'utf8').startsWith('#!/usr/bin/env node\n')).toBe(true)
  if (built) expect(readFileSync(`${root}dist/interchange/cli.js`, 'utf8').startsWith('#!/usr/bin/env node\n')).toBe(true)
  const e = pkg.exports['./interchange']!
  expect(e.default).toBe('./dist/interchange/check.js')
  const mod = await import(built ? `${pkg.name}/interchange` : `${root}interchange/check.ts`) as Record<string, unknown>
  for (const fn of ['checkDocument', 'goalsOf', 'toInterchange', 'fromInterchange']) expect(typeof mod[fn]).toBe('function')
})

// The tarball as npm packs it (built first where dist/ isn't): every export's module and types, the bin, and every
// file a front end runs beside its module, for every language (its reader, its harness, Solidity's replay contracts),
// each one the code names too. (0.43.0's lacked sol/harness.py and Replay.sol: a .sol check waited forever.)
test('the packed tarball holds every export, the bin and every runtime asset the code references', () => {
  if (!existsSync(`${root}dist/core/dsl.js`)) execFileSync('bun', ['scripts/build.ts'], {cwd: root, stdio: 'ignore'})
  const pack = (dir: string) => new Set((JSON.parse(execFileSync('npm', ['pack', '--dry-run', '--json', '--ignore-scripts'], {cwd: dir, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore']})) as {files: {path: string}[]}[])[0]!.files.map(f => f.path))
  const files = pack(root)
  const missing = (want: string[]) => want.filter(f => !files.has(f))
  expect(missing(Object.values(pkg.exports).filter(e => typeof e === 'object').flatMap(e => [e.default, e.types].map(p => p.replace(/^\.\//, ''))))).toEqual([])
  expect(missing(Object.values(pkg.bin ?? {}))).toEqual([])
  const assets = runtimeAssets()
  for (const dir of ['py', 'rb', 'ex', 'jvm', 'rs', 'go', 'swift', 'sol']) expect(assets.some(f => f.startsWith(`${dir}/`))).toBe(true)
  expect(missing(assets.map(f => `dist/core/${f}`))).toEqual([])
  const named = referenced()
  expect(named).toContain('sol/harness.py')
  expect(named).toContain('sol/Replay.sol')
  expect(named).toContain('py/harness.py')
  expect(named.filter(f => !(f.endsWith('/') ? [...files].some(p => p.startsWith(`dist/core/${f}`)) : files.has(`dist/core/${f}`)))).toEqual([])
  const cli = pack(`${root}packages/cli`)
  expect([...cli].filter(f => f !== 'package.json')).toEqual(['bin.js'])
}, 300_000)

// A check never waits on a harness that can't start: a missing asset is a clear error, and a harness that exits before
// it answers is reported, not waited for.
test('a missing asset is a clear error; a harness that exits before it answers is reported, not waited on', async () => {
  const {asset, checkStep} = await import('./extract-step.ts')
  expect(asset('sol/harness.py')).toMatch(/core\/sol\/harness\.py$/)
  expect(() => asset('sol/missing.py')).toThrow(/gdp-wired's sol\/missing\.py is missing from its install .*reinstall gdp-wired/)
  const read = {model: {state: [], inputs: [], params: [], outputs: [], maps: [], events: []}, leaves: [], ctor: [], answers: [], kept: false, arms: [], stores: {}, ints: {}, args: {}, results: {}} as never
  const t0 = Date.now()
  const ev = checkStep({cmd: 'sh', args: ['-c', 'exit 3'], hello: {}}, read, {} as never, {} as never, {})
  expect(ev.mismatch).toMatch(/the harness exited \(status 3\) before it answered/)
  expect(Date.now() - t0).toBeLessThan(20_000)
}, 60_000)
