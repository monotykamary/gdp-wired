// k-induction: laws the kernel's induction (one step) doesn't prove, proven over k steps in a row (core/kind.ts; the
// certificate is kernel.ts's checkKInduction, its Lean twin KInd.lean's kind_sound). A value clamped on its way into a
// pipeline of registers is within the cap when it comes out: one step from a state where only the output is known to
// be within it says nothing (the register before it may hold anything), but over as many steps as the pipeline is long
// every value on the way came in clamped. A token passed around a ring of slots stays in it. A variant that lets one
// value in unclamped is refused with a run.
// With --lean, each law as a Lean theorem through KInd.lean's kind_sound:
//   bun examples/kinduction.ts
//   bun examples/kinduction.ts --lean > lean-kernel/KindExamples.lean
import {min, nat, proveRule, rule} from '../core/dsl.ts'
import {type LeanItem, toLean} from '../lean-kernel/emit.ts'
import {conjunction} from '../core/kind.ts'

// A pipeline of three registers: a := min(x, cap), b := a, out := b.
const pipeline = (bug?: 'unclamped') => rule('pipeline').params({cap: nat}).inputs({x: nat}).state({a: 0, b: 0, out: 0})
  .step(({x, cap, a, b}) => ({a: bug ? x : min(x, cap), b: a, out: b}))
// A ring of four slots passing one token on each tick (each slot takes the one before it); the law: slot 1 holds at most
// one. (Were a tick allowed to pass nothing on, no k would do: slot 1 could keep its token for any k ticks while slot 4
// holds anything.)
const ring = () => rule('ring').state({s1: 1, s2: 0, s3: 0, s4: 0}).step(({s1, s2, s3, s4}) => ({s1: s4, s2: s1, s3: s2, s4: s3}))
const cases = [
  {r: pipeline(), law: (r: ReturnType<typeof pipeline>) => r.law('out within cap', ({out, cap}) => out.atMost(cap)), k: 3},
  {r: ring(), law: (r: ReturnType<typeof ring>) => r.law('slot 1 holds at most one token', ({s1}) => s1.atMost(1)), k: 4},
] as const

if (process.argv.includes('--lean')) {
  const items: LeanItem[] = cases.map(c => ({id: c.r.machine.name, kInduction: {machine: c.r.machine, laws: c.r.kindLaws(), law: conjunction([c.law(c.r as never)])}}))
  console.log(toLean(items, {title: 'Laws proven by k-induction (examples/kinduction.ts)'}))
  process.exit(0)
}
let failed = false
for (const c of cases) {
  const law = c.law(c.r as never), t0 = performance.now(), one = proveRule(c.r, [law], {search: false}), v = proveRule(c.r, [law]), ms = performance.now() - t0
  const ok = !one.proven && v.proven && v.checked && v.k === c.k
  failed ||= !ok
  console.log(`${ok ? 'ok  ' : 'FAIL'} ${c.r.machine.name}: ${law.name}: one step ${one.proven ? 'PROVES IT' : 'does not prove it'}; ${v.proven ? (v.checked ? `proven by k-induction, k = ${v.k}` : 'KERNEL REJECTS') : `NOT PROVEN (${v.why ?? v.stuck})`} in ${ms.toFixed(0)} ms`)
}
const b = pipeline('unclamped'), bv = proveRule(b, [b.law('out within cap', ({out, cap}) => out.atMost(cap))])
failed ||= bv.proven || !bv.run
console.log(`${!bv.proven && bv.run ? 'ok  ' : 'FAIL'} the unclamped pipeline: ${bv.proven ? 'PROVEN' : `refused${bv.run ? `, a run of ${bv.run.trace.length} requests` : ''}`}`)
if (failed) process.exit(1)
