// Laws over many steps in a row: the budget rule's spend over k requests is at most k times the per-request cap, for k
// from 2 to 32 (to 16 for Lean, which takes minutes past that), and a variant that lets one request through uncapped is
// refused. Each step's case (under the budget or not, the request under the cap or not) multiplies the cases; the
// prover proves a fact about each step's value that holds either way first (a cut: its failing side decides that step
// alone), so the proof grows with k, not with 4^k; each step's state is named in the goal (n~j), so its terms stay small
// too.
// With --lean, every law as a Lean theorem, for lean-kernel:
//   bun examples/steps.ts            # prove and refuse, with times
//   bun examples/steps.ts --lean > lean-kernel/KSteps.lean
import {min, nat, proveSteps, rule, when} from '../core/dsl.ts'
import {type LeanItem, toLean} from '../lean-kernel/emit.ts'

const budget = (bug?: 'one request uncapped') => rule('budget').params({b: nat, m: nat}).inputs({c: nat, big: nat}).state({s: 0})
  .step(({b, m, c, s, big}) => ({s: when(s.lt(b), s.plus(bug ? when(big.eq(1), c, min(c, m)) : min(c, m)), s)}))
const within = (r: ReturnType<typeof budget>) => r.law('spend stays within b + m', ({s, b, m}) => s.atMost(b.plus(m)))
const over = (r: ReturnType<typeof budget>, k: number) => r.stepsLaw(`${k} requests spend at most ${k}m`, k, ({s, m}, last) => last.s.atMost(s.plus(m.times(k))))
const ks = [2, 4, 8, 12, 16]

if (process.argv.includes('--lean')) {
  const r = budget(), items: LeanItem[] = [{id: 'budget_steps', machine: r.machine, laws: [within(r)], stepLaws: ks.map(k => over(r, k))}]
  console.log(toLean(items, {title: 'Laws over up to 16 steps (examples/steps.ts)'}))
  process.exit(0)
}
let failed = false
for (const k of [...ks, 32]) {
  const t0 = performance.now(), v = proveSteps(budget(), [within(budget())], [over(budget(), k)]), ms = performance.now() - t0
  const b = proveSteps(budget('one request uncapped'), [within(budget('one request uncapped'))], [over(budget('one request uncapped'), k)])
  const ok = v.proven && v.checked && !b.proven
  failed ||= !ok
  console.log(`${ok ? 'ok  ' : 'FAIL'} ${k} steps: ${v.proven ? (v.checked ? 'proven' : 'KERNEL REJECTS') : `NOT PROVEN (${v.why ?? v.stuck})`} in ${ms.toFixed(0)} ms; uncapped variant ${b.proven ? 'PROVEN' : 'refused'}`)
}
if (failed) process.exit(1)
