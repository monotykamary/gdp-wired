// Builds gdp-wired-check from the trusted files as they are: the CLI bundle (interchange/dist/gdp-wired-check.js, for
// node or bun), a compiled executable (gdp-wired-check, with --compile) and the WebAssembly module
// (gdp-wired-check.wasm, with --wasm: Javy 9.1.0, at $JAVY). Prints each bundle's inputs, and the trusted files' git
// blob ids, which must be the ones the commit holds (nothing trusted changed to build it).
//   bun interchange/build.ts [--compile] [--wasm]
import {createHash} from 'node:crypto'
import {mkdirSync, readFileSync} from 'node:fs'
import {join} from 'node:path'

const here = import.meta.dir, root = join(here, '..'), dist = join(here, 'dist')
mkdirSync(dist, {recursive: true})
const trusted = ['kernel/kernel.ts', 'kernel/cyclic.ts', 'core/check.ts']
const run = (cmd: string[], cwd = root) => { const r = Bun.spawnSync(cmd, {cwd, stdout: 'pipe', stderr: 'pipe'}); if (r.exitCode !== 0) throw new Error(`${cmd.join(' ')}: ${r.stderr.toString()}`); return r.stdout.toString().trim() }
// A file's git blob id (sha1 of "blob <size>\0" and its bytes), computed here, so a copy without .git (a container's)
// still says which trusted files it was built from; where git is, each is compared with the commit's.
const blob = (f: string) => { const b = readFileSync(join(root, f)); return createHash('sha1').update(`blob ${b.length}\0`).update(b).digest('hex') }
for (const f of trusted) {
  const disk = blob(f)
  let committed: string | undefined
  try { committed = run(['git', 'rev-parse', `HEAD:${f}`]) } catch { committed = undefined }
  console.log(`${f}: ${disk}${committed === undefined ? ' (no git here to compare)' : disk === committed ? ' (as committed)' : ` CHANGED (committed ${committed})`}`)
  if (committed !== undefined && disk !== committed) process.exit(1)
}
const bundle = async (entry: string, out: string, target: 'node' | 'browser') => {
  // (metafile: the modules bundled, which bun 1.4 reports and its types don't name yet)
  const r = await Bun.build({entrypoints: [join(here, entry)], outdir: dist, naming: out, target, format: 'esm', minify: false, ...{metafile: true}}) as Awaited<ReturnType<typeof Bun.build>> & {metafile?: {inputs: Record<string, unknown>}}
  if (!r.success) throw new Error(r.logs.map(l => l.message).join('\n'))
  const inputs = Object.keys(r.metafile?.inputs ?? {}).map(p => p.replace(/^.*?(?=(kernel|core|interchange)\/)/, ''))
  console.log(`${out}: ${(readFileSync(join(dist, out)).length / 1024).toFixed(1)} KB from ${inputs.join(', ')}`)
  for (const f of trusted) if (!inputs.includes(f)) throw new Error(`${out} is not built from ${f}`)
}
await bundle('cli.ts', 'gdp-wired-check.js', 'node')
if (process.argv.includes('--compile')) { run(['bun', 'build', '--compile', join(here, 'cli.ts'), '--outfile', join(dist, 'gdp-wired-check')]); console.log('gdp-wired-check: compiled') }
if (process.argv.includes('--wasm')) {
  const javy = process.env.JAVY
  if (!javy) throw new Error('--wasm: set JAVY to a Javy 9.1.0 binary (github.com/bytecodealliance/javy/releases/tag/v9.1.0)')
  await bundle('wasm.ts', 'check-wasm.js', 'browser')
  run([javy, 'build', '-J', 'javy-stream-io=y', '-J', 'text-encoding=y', '-C', 'source=omitted', '-o', join(dist, 'gdp-wired-check.wasm'), join(dist, 'check-wasm.js')])
  console.log(`gdp-wired-check.wasm: ${(readFileSync(join(dist, 'gdp-wired-check.wasm')).length / 1024).toFixed(1)} KB (${run([javy, '--version'])})`)
}
