// The npm build: the library's six modules to dist/ as JS with declarations. tsc rewrites the `.ts` imports of the JS
// to `.js` but leaves them in the declarations, so they are rewritten here too.
import {copyFileSync, mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'

const root = join(import.meta.dir, '..'), dist = join(root, 'dist')
rmSync(dist, {recursive: true, force: true})
const tsc = Bun.spawnSync(['bunx', 'tsc', '-p', 'tsconfig.build.json'], {cwd: root, stdout: 'inherit', stderr: 'inherit'})
if (tsc.exitCode !== 0) process.exit(tsc.exitCode ?? 1)
for (const f of readdirSync(dist, {recursive: true, encoding: 'utf8'}).filter(f => f.endsWith('.d.ts'))) {
  const path = join(dist, f), text = readFileSync(path, 'utf8')
  writeFileSync(path, text.replace(/(from '\.{1,2}\/[^']+)\.ts'/g, "$1.js'"))
}
// The Python front end's reader and harness, run from beside it (python3 is needed only when it is called).
mkdirSync(join(dist, 'core', 'py'), {recursive: true})
for (const f of ['reader.py', 'harness.py']) copyFileSync(join(root, 'core', 'py', f), join(dist, 'core', 'py', f))
// The Ruby front end's reader and harness, run from beside it (ruby is needed only when it is called).
mkdirSync(join(dist, 'core', 'rb'), {recursive: true})
for (const f of ['reader.rb', 'harness.rb']) copyFileSync(join(root, 'core', 'rb', f), join(dist, 'core', 'rb', f))
// The Rust front end's reader (built with cargo where it is first called) beside it.
mkdirSync(join(dist, 'core', 'rs', 'src'), {recursive: true})
for (const f of ['Cargo.toml', 'Cargo.lock', 'src/main.rs']) copyFileSync(join(root, 'core', 'rs', f), join(dist, 'core', 'rs', f))
const left = readdirSync(dist, {recursive: true, encoding: 'utf8'}).filter(f => /\.(js|d\.ts)$/.test(f) && /from ['"]\.{1,2}\/[^'"]+\.ts['"]/.test(readFileSync(join(dist, f), 'utf8')))
if (left.length) throw new Error(`.ts imports left in ${left.join(', ')}`)
console.log(`dist: ${readdirSync(dist, {recursive: true}).length} entries`)
