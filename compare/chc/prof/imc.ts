// Interpolation over the unrolling alone (core/interp.ts's imc): `bun compare/chc/prof/imc.ts <task.smt2> [--ms 55000]`
// (`--tools imc` in modal_chc.py). Answers as solve.ts does, each answer checked the same way: sat where the kernel
// proves the law with the fixed point as a law beside it (proveRule, no search), unsat where translate.ts's
// checkDerivation confirms the run against the CHC. What it measures: the search alone, on the second CPU's budget.
import {readFileSync} from 'node:fs'
import {parseChc} from '../chc.ts'
import {build, checkDerivation, requestOf, stepsOf} from '../translate.ts'
import {imc} from '../../../core/interp.ts'
import {proveRule} from '../../../core/dsl.ts'
import {counted, withDeadline} from '../../../kernel/prove.ts'

const args = process.argv.slice(2), file = args[0]!
const ms = Number(args[args.indexOf('--ms') + 1] ?? 55_000) || 55_000, t0 = performance.now(), wall = t0 + ms
const say = (o: object) => { console.log(JSON.stringify({task: file, ms: Math.round(performance.now() - t0), ...o})); if ((o as {stage?: string}).stage === 'answer') process.exit(0) }
const b = build(parseChc(readFileSync(file, 'utf8'))), r = b.rule, m = r.machine
const steps: [number, string, number][] = []
const out = counted(250, () => imc(m, b.law, {until: Infinity, wall, kinds: r.kindLaws().map(l => l.holds), progress: (k, what, info) => steps.push([k, what[0]!, info.parts!])}), true)
say({stage: 'imc', depths: steps, ...('why' in out ? {why: out.why} : {}), k: out.k})
if ('run' in out) {
  const raws = out.run.trace.map(t => requestOf(b, t as Record<string, unknown>)), bad = checkDerivation(b, parseChc(readFileSync(file, 'utf8')), stepsOf(b, raws))
  if (bad) say({stage: 'imc', refused: bad})
  else say({stage: 'answer', answer: 'unsat', by: 'imc', steps: raws.length})
} else if ('inv' in out) {
  const t1 = performance.now()
  const v = withDeadline(wall, () => proveRule(r, [b.law, {name: 'imc', holds: out.inv}], {search: false}))
  say({stage: 'prove', proven: v.proven, checked: v.checked, parts: out.parts, proveMs: Math.round(performance.now() - t1)})
  if (v.proven && v.checked) say({stage: 'answer', answer: 'sat', by: 'imc', k: out.k})
}
say({stage: 'answer', answer: 'unknown'})
