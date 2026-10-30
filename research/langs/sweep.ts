// What the subset reads of the files a language corpus cites: every method of every class (and every module function)
// they declare, each extracted alone, one JSON line each; where it extracts, the laws `check` proposes with their
// verdicts. Each research/langs/<lang>/run.ts calls it with `--sweep <out.jsonl>`; `bun research/langs/sweep.ts <base>
// <cand>` compares two sweeps (the units refused for a loop or a try in one that the other reads, and every unit both
// read whose rule differs).
import {appendFileSync, readFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import type {SModule} from '../../core/extract-step.ts'
import {type Extraction, toSource} from '../../core/extract.ts'

type Lang = 'python' | 'ruby' | 'java' | 'kotlin' | 'rust' | 'swift' | 'c' | 'cpp'
// (the files swept already, by path: several specs cite one file)
const swept = new Set<string>()

export type Unit = {label: string, opts: Record<string, unknown>}
const CTORS = new Set(['__init__', '__post_init__', 'initialize', 'new', 'init', '<init>'])
// Each class's methods (but its constructor), each alone, the class named as `name` gives it; each module function.
export function unitsOf(mod: SModule, name: (rec: SModule['recs'][string]) => string = r => r.short): Unit[] {
  const out: Unit[] = [], seen = new Set<string>()
  for (const e of mod.entries) {
    if (e.k === 'class') {
      const r = mod.recs[e.rec]
      if (!r) continue
      for (const [m, id] of Object.entries(r.methods)) if (id && !CTORS.has(m) && !seen.has(`${r.name}.${m}`)) { seen.add(`${r.name}.${m}`); out.push({label: `${r.short}.${m}`, opts: {entry: name(r), methods: [m]}}) }
    } else if (e.k === 'func') out.push({label: e.id, opts: {entry: [e.id]}})
  }
  for (const f of Object.values(mod.funcs)) if (!f.cls && f.id === f.name && !out.some(u => u.label === f.id)) out.push({label: f.id, opts: {entry: [f.id]}})
  return out
}
// Each unit extracted (the caller's extraction, given the unit's options), its line appended to `out`.
// (laws: the proposed laws proven, where the checkout has them: core/cli.ts's proposedLaws)
export async function sweep(out: string, lang: Lang, file: string, units: () => Unit[], extract: (o: Record<string, unknown>) => Extraction, laws = !process.argv.includes('--no-laws')) {
  if (swept.has(file)) return
  swept.add(file)
  const propose = laws ? (await import('../../core/cli.ts') as {proposedLaws?: (x: Extraction, lang: Lang, ms?: number) => {shown: {name: string, verdict: string}[], broken: number}}).proposedLaws : undefined
  let us: Unit[]
  try { us = units() } catch (e) { appendFileSync(out, `${JSON.stringify({lang, file, unit: '*', ok: false, error: String((e as Error).message).slice(0, 300)})}\n`); return }
  for (const u of us) {
    const t0 = performance.now()
    let x: Extraction
    try { x = extract(u.opts) } catch (e) { appendFileSync(out, `${JSON.stringify({lang, file, unit: u.label, ok: false, error: String((e as Error).message).slice(0, 300)})}\n`); continue }
    const src = x.ok ? toSource(x) : undefined
    const line: Record<string, unknown> = {lang, file, unit: u.label, ok: x.ok, ms: Math.round(performance.now() - t0)}
    if (!x.ok) line.refusal = x.refusals[0]
    else {
      line.rule = createHash('sha1').update(src!).digest('hex').slice(0, 12)
      if (propose) { try { const p = propose(x, lang); line.laws = p.shown.map(l => ({name: l.name, verdict: l.verdict})); line.broken = p.broken } catch (e) { line.lawError = String((e as Error).message).slice(0, 200) } }
    }
    appendFileSync(out, `${JSON.stringify(line)}\n`)
    console.log(`  sweep ${u.label}: ${x.ok ? 'extracted' : `refused (${x.refusals[0]?.what.slice(0, 120)})`}`)
  }
}

// --- the comparison ---------------------------------------------------------------------------------------------------
const LOOPY = /a loop|loop \(|try|except|rescue|catch|comprehension|a block \(a closure\)|continue|a break|generator/
if (import.meta.main) {
  const [a, b] = process.argv.slice(2)
  const read = (f: string) => new Map(readFileSync(f, 'utf8').split('\n').filter(Boolean).map(l => JSON.parse(l) as Record<string, unknown>).map(r => [[r.lang, r.file, r.unit].map(String).join(' '), r]))
  const base = read(a!), cand = read(b!)
  const gained: unknown[] = [], lost: unknown[] = [], changed: unknown[] = [], moved: unknown[] = []
  let loopy = 0
  for (const [k, x] of base) {
    const y = cand.get(k)
    if (!y) continue
    const why = (x.refusal as {what?: string} | undefined)?.what ?? ''
    if (!x.ok && LOOPY.test(why)) loopy++
    if (!x.ok && y.ok) gained.push({unit: k, was: why, laws: y.laws})
    else if (x.ok && !y.ok) lost.push({unit: k, now: (y.refusal as {what?: string} | undefined)?.what})
    else if (x.ok && y.ok && x.rule !== y.rule) changed.push({unit: k})
    else if (!x.ok && !y.ok && LOOPY.test(why) && why !== (y.refusal as {what?: string} | undefined)?.what) moved.push({unit: k, was: why, now: (y.refusal as {what?: string} | undefined)?.what})
  }
  console.log(JSON.stringify({units: base.size, refusedForLoopOrTry: loopy, gained: gained.length, lost: lost.length, changed: changed.length, movedFurther: moved.length}, null, 1))
  for (const g of gained) console.log(`gained ${JSON.stringify(g)}`)
  for (const g of lost) console.log(`lost ${JSON.stringify(g)}`)
  for (const g of changed) console.log(`changed ${JSON.stringify(g)}`)
  for (const g of moved) console.log(`moved ${JSON.stringify(g)}`)
}
