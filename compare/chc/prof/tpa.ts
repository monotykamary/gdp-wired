// Transition power abstraction alone (core/tpa.ts): `bun compare/chc/prof/tpa.ts <task.smt2> [--ms 55000]` (`--tools
// tpa` in modal_chc.py). Answers as solve.ts does, each answer checked the same way: sat where the kernel proves the
// law with the invariant's conjuncts as laws beside it (proveRule, no search), unsat where translate.ts's
// checkDerivation confirms the run against the CHC. What it measures: the search alone.
import {readFileSync} from 'node:fs'
import {parseChc} from '../chc.ts'
import {build, checkDerivation, requestOf, stepsOf} from '../translate.ts'
import {tpa} from '../../../core/tpa.ts'
import {proveRule} from '../../../core/dsl.ts'
import {counted, withDeadline} from '../../../kernel/prove.ts'

const args = process.argv.slice(2), file = args[0]!
const ms = Number(args[args.indexOf('--ms') + 1] ?? 55_000) || 55_000, t0 = performance.now(), wall = t0 + ms
const say = (o: object) => console.log(JSON.stringify({task: file, ms: Math.round(performance.now() - t0), ...o}))
const chc = parseChc(readFileSync(file, 'utf8')), b = build(chc), r = b.rule, m = r.machine
const levels: [number, string, number][] = []
const out = counted(250, () => tpa(m, b.law, {until: Infinity, wall, kinds: r.kindLaws().map(l => l.holds), progress: (n, what) => levels.push([n, what, Math.round(performance.now() - t0)])}), true)
say({stage: 'tpa', levels, level: out.level, ...('why' in out ? {why: out.why} : {})})
if ('run' in out) {
  const raws = out.run.trace.map(t => requestOf(b, t as Record<string, unknown>)), bad = checkDerivation(b, chc, stepsOf(b, raws))
  if (bad) say({stage: 'tpa', refused: bad})
  else say({stage: 'answer', answer: 'unsat', by: 'tpa', steps: raws.length})
} else if ('inv' in out) {
  const t1 = performance.now()
  const v = withDeadline(wall, () => proveRule(r, [b.law, ...out.inv.map((holds, i) => ({name: `tpa ${i}`, holds}))], {search: false}))
  say({stage: 'prove', proven: v.proven, checked: v.checked, laws: out.inv.length, proveMs: Math.round(performance.now() - t1)})
  if (v.proven && v.checked) say({stage: 'answer', answer: 'sat', by: 'tpa', level: out.level})
}
say({stage: 'answer', answer: 'unknown'})
