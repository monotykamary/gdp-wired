// Every front end as a user imports it: each one's subpath in package.json's exports, its types and its module built
// from a file the build compiles, the files it runs beside it copied by the build, and its function there. Imported
// through the package's own name where it is built (dist/), else from the source each export is built from.
import {expect, test} from 'bun:test'
import {existsSync, readFileSync} from 'node:fs'

const root = new URL('../', import.meta.url).pathname
const pkg = JSON.parse(readFileSync(`${root}package.json`, 'utf8')) as {name: string, bin?: Record<string, string>, exports: Record<string, {types: string, default: string}>, files: string[]}
const build = JSON.parse(readFileSync(`${root}tsconfig.build.json`, 'utf8')) as {files: string[]}
const buildScript = readFileSync(`${root}scripts/build.ts`, 'utf8')
// The front ends: the subpath, the function a user calls, and the files it runs beside its module (copied by the build).
const FRONT: [string, string, string[]][] = [
  ['./extract', 'extract', []], ['./effect', 'extractEffect', []],
  ['./extract-py', 'extractPython', ['py/reader.py', 'py/harness.py']], ['./extract-rb', 'extractRuby', ['rb/reader.rb', 'rb/harness.rb']],
  ['./extract-ex', 'extractElixir', ['ex/reader.exs', 'ex/harness.exs', 'ex/json.exs']], ['./extract-rs', 'extractRust', ['rs/Cargo.toml', 'rs/src/main.rs']],
  ['./extract-c', 'extractC', []], ['./extract-cpp', 'extractCpp', []], ['./extract-java', 'extractJava', ['jvm/JavaReader.java', 'jvm/Harness.java']],
  ['./extract-kotlin', 'extractKotlin', ['jvm/KtReader.java']], ['./extract-go', 'extractGo', ['go/go.mod', 'go/reader.go']],
]
const built = existsSync(`${root}dist/core/dsl.js`)

for (const [sub, fn, beside] of FRONT) {
  test(`${sub}: exported, typed, built and its ${fn} there`, async () => {
    const e = pkg.exports[sub]
    expect(e).toBeDefined()
    const src = e!.default.replace(/^\.\/dist\//, '').replace(/\.js$/, '.ts')
    expect(e!.types).toBe(e!.default.replace(/\.js$/, '.d.ts'))
    expect(build.files).toContain(src)
    for (const f of beside) {
      expect(existsSync(`${root}core/${f}`)).toBe(true)
      expect(buildScript).toContain(`'${f.slice(f.indexOf('/') + 1)}'`)
      if (built) expect(existsSync(`${root}dist/core/${f}`)).toBe(true)
    }
    const mod = await import(built ? `${pkg.name}/${sub.slice(2)}` : `${root}${src}`) as Record<string, unknown>
    expect(typeof mod[fn]).toBe('function')
  })
}
