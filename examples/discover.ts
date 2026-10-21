// Lemmas nobody stated, found (core/discover.ts): for the suite (`bun examples/discover.ts`), core/discover.test.ts and
// lean-kernel/package-check.ts, which checks the rules made again with what was found.
//   - retry with backoff (examples/lemmas.ts's, its delay stating no lemma): the delay at most 64 and at least 1 are found
//   - area: squares, f(x + 1) = f(x) + 2x + 1, stating no lemma: its closed form f(x) = x·x is found
// (The recurrences go by names of their own here, apart from examples/lemmas.ts's, which state their lemmas: the Lean
// check holds both.)
//   - invoices (examples/invoices.ts, stating no lemma): the taxable part within the total, at every prefix
//   - the org chart (examples/folds.ts), its reports' lemmas taken out: the reports cost at most the cap per head, and
//     are at least as many as they are deep
//   - and a law that doesn't hold stays unproven: the retries' next try within 32 of the last request
import {type Law} from '../core/machine.ts'
import {type StepLaw, fold, max, min, nat, oneOf, proveFold, recur, rule, when} from '../core/dsl.ts'
import {discover, discoverFold} from '../core/discover.ts'
import {invoiceLaws, invoiceSteps, invoices} from './invoices.ts'

export const backoff = () => recur('backoff', {zero: 1, next: (_, d) => min(d.times(2), 64)})
export const retries = () => rule('retry with backoff').inputs({op: oneOf('fail', 'ok'), now: nat}).state({tries: 0, next: 0, last: 0}).fns({delay: backoff()})
  .assume(({now, last}) => now.atLeast(last))
  .flags(({op, now, next}) => ({retry: op.is('fail').and(now.atLeast(next)), done: op.is('ok').and(now.atLeast(next))}))
  .step(({now, tries, next, retry, done, delay}) => ({tries: when(retry, tries.plus(1), when(done, 0, tries)), next: when(retry, now.plus(delay(tries)), next), last: now}))
export const retryLaws = (r = retries()): Law[] => [r.law('the next try is at most 64 after the last request', ({next, last}) => next.atMost(last.plus(64)))]
export const retrySteps = (r = retries()): StepLaw[] => [r.stepLaw('a failure waits at least a tick', ({now, retry}, after) => retry.implies(after.next.gt(now)))]
export const foundRetries = () => { const r = retries(); return discover(r, retryLaws(r), retrySteps(r)) }
export const squares = () => recur('square', {zero: 0, next: (x, p) => p.plus(x.times(2)).plus(1)})
export const area = () => rule('area').inputs({}).state({n: 0, a: 0}).fns({sq: squares()}).step(({n, sq}) => ({n: n.plus(1), a: sq(n.plus(1))}))
export const areaLaws = (r = area()): Law[] => [r.law('the area is n·n', ({a, n}) => a.eq(n.mul(n)))]
export const foundArea = () => { const r = area(); return discover(r, areaLaws(r)) }
export const foundInvoices = () => { const r = invoices('states no lemma'); return discover(r, invoiceLaws(r), invoiceSteps(r)) }
export const orgChart = () => fold('org chart').params({cap: nat}).inputs({pay: nat})
  .leaf(({pay, cap}) => ({cost: min(pay, cap), heads: 1, depth: 0}))
  .children({cost: 0, heads: 0, depth: 0}, (acc, kid) => ({cost: acc.cost.plus(kid.cost), heads: acc.heads.plus(kid.heads), depth: max(acc.depth, kid.depth.plus(1))}))
  .node(({pay, cap}, kids) => ({cost: kids.cost.plus(min(pay, cap)), heads: kids.heads.plus(1), depth: kids.depth}))
export const orgChartLaws = (f = orgChart()): Law[] => [
  f.law('the roll-up is at most the cap per head', ({cost, heads, cap}) => cost.atMost(heads.mul(cap))),
  f.law('a chart is at least as wide as it is deep', ({depth, heads}) => depth.lt(heads)),
]
export const foundOrgChart = () => { const f = orgChart(); return discoverFold(f, orgChartLaws(f)) }
export const tooSoon = () => { const r = retries(); return discover(r, [r.law('the next try is at most 32 after the last request', ({next, last}) => next.atMost(last.plus(32)))]) }

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const [what, out] of [['retry with backoff', foundRetries], ['area', foundArea], ['invoices', foundInvoices]] as const) {
    const o = out()
    results.push([what, o.verdict.proven && o.verdict.checked, true])
    for (const [n, f] of Object.entries(o.found)) console.log(`  ${what}, ${n}: ${[...(f.lemmas ?? []), ...(f.between ?? [])].join('; ')}`)
  }
  const o = foundOrgChart(), f = orgChart()
  results.push(['org chart', o.verdict.proven && o.verdict.checked, true], ['org chart, as stated', proveFold(f, orgChartLaws(f)).proven, false])
  console.log(`  org chart: ${o.found.join('; ')}`)
  results.push(['retries: next within 32 of the last request', tooSoon().verdict.proven, false])
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
