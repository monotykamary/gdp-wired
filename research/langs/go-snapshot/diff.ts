// The port's differential test, no Go needed: every reading the baseline jobs captured ($GDP_GO_CAPTURE in
// research/langs/go-capture.json: the reader's JSON, the options, and what readGo made of it, or its refusal) read
// again by core/extract-go.ts now and compared as JSON, byte for byte. With --extra, every struct of every package
// captured (its exported methods, then each method alone) read by the baseline's front end (466c0ab, put beside it as
// core/extract-go-old.ts while it runs, never committed) and by today's.
//
//   bun research/langs/go-snapshot/diff.ts runs/langs/cap/cap-tests.jsonl runs/langs/cap/cap-rw.jsonl [--extra] [-v]
import {existsSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {execFileSync} from 'node:child_process'
import {join} from 'node:path'
import {type GoPkg, probeGoFunc, readGo} from '../../../core/extract-go.ts'
import {Refusal} from '../../../core/extract-read.ts'

const args = process.argv.slice(2), files = args.filter(a => !a.startsWith('-')), verbose = args.includes('-v')
const ser = (x: unknown) => JSON.stringify(x, (_, v) => (v instanceof Map ? [...v] : v instanceof WeakMap ? {} : v))
const run = (f: () => unknown) => { try { return ser({read: f()}) } catch (e) { if (e instanceof Refusal) return ser({refusal: {where: e.where, what: e.what}}); return ser({crash: String((e as Error).stack ?? e).split('\n').slice(0, 4).join(' | ')}) } }
let same = 0, differ = 0
const first = (a: string, b: string) => { let i = 0; while (i < a.length && a[i] === b[i]) i++; return `@${i}\n    before …${a.slice(Math.max(0, i - 150), i + 250)}\n    after  …${b.slice(Math.max(0, i - 150), i + 250)}` }
const report = (label: string, before: string, after: string) => {
  if (before === after) { same++; return }
  differ++
  console.log(`\n${label}: ${first(before, after)}`)
}
const pkgs = new Map<string, GoPkg>()
for (const f of files) {
  readFileSync(f, 'utf8').trim().split('\n').forEach((line, i) => {
    const x = JSON.parse(line) as {k: string, pkg: GoPkg, opts?: {entry: string}, read?: unknown, refusal?: unknown, name?: string, out?: unknown}
    pkgs.set(JSON.stringify(x.pkg.funcs.map(g => g.p)) + x.pkg.package, x.pkg)
    if (x.k === 'probe') { report(`${f}#${i} probe ${x.name}`, ser(x.out), ser(probeGoFunc(x.pkg, x.name!))); return }
    const before = x.refusal ? ser({refusal: x.refusal}) : ser({read: x.read})
    report(`${f}#${i} ${x.opts!.entry}`, before, run(() => readGo(x.pkg, x.opts as never)))
  })
}
console.log(`\ncaptured: ${same} the same, ${differ} differ`)
if (args.includes('--extra')) {
  const root = join(import.meta.dir, '../../..'), old = join(root, 'core/extract-go-old.ts')
  if (!existsSync(old)) writeFileSync(old, execFileSync('git', ['show', '466c0ab:core/extract-go.ts'], {cwd: root, encoding: 'utf8'}))
  const {readGo: readOld} = await import(old) as {readGo: typeof readGo}
  const s0 = same, d0 = differ
  for (const pkg of pkgs.values()) for (const t of pkg.types) {
    const ms = pkg.funcs.filter(f => f.recv?.type === t.name && f.body).map(f => f.name)
    if (!ms.length) continue
    for (const methods of [undefined, ...ms.map(m => [m])]) {
      const opts = {entry: t.name, ...(methods ? {methods} : {})}
      for (const onError of [undefined, 'discard'] as const) {
        const o = {...opts, ...(onError ? {onError} : {})}
        report(`extra ${pkg.package}.${t.name} ${methods?.join() ?? '*'}${onError ? ' discard' : ''}`, run(() => readOld(pkg, o)), run(() => readGo(pkg, o)))
      }
    }
  }
  rmSync(old)
  console.log(`extra: ${same - s0} the same, ${differ - d0} differ`)
}
if (verbose) console.log(`${pkgs.size} packages`)
process.exit(differ ? 1 : 0)
