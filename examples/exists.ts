// There exists (core/exists.ts): laws that say some value is a witness, each proven through one the prover finds, and
// a broken variant of each refused. `bun examples/exists.ts` proves and refuses them; `--lean` prints the Lean export
// (`--lean cyclic`, from cyclic certificates), where each law is stated as ∃ and proven by ⟨witness, proof⟩.
//   - a counter that steps by two: it is always 2k (a ghost: k + 1 or k − 1 with each step, chosen by the kernel's
//     counterexamples); stepping by three, a run reaches 3, which no k makes 2k
//   - a set that only grows: once anything was added, some name is in (a ghost key: the request's name on an add, else
//     the one before), where examples/quantifiers.ts kept the last name in the state; with a drop, a run empties it
//   - a ledger whose transfers are whole multiples of 5 (an existential in the assumption: a value each request brings,
//     the runtime finds it): its balance is always 5j for some integer j (a ghost: j plus the request's own); a fee of
//     1 a transfer breaks it
//   - a window [lo, hi]: some time is in it (a witness term: lo); given hi + 1 as the witness, the kernel refuses it
import {exists, int, nat, oneOf, proveRule, rule, when} from '../core/dsl.ts'
import type {Law} from '../core/machine.ts'

export const evens = (bug?: 'steps by 3') => rule('evens').inputs({go: oneOf('up', 'down', 'stay')}).state({x: 0})
  .step(({go, x}) => ({x: when(go.is('up'), x.plus(bug ? 3 : 2), when(go.is('down').and(x.atLeast(2)), x.minus(2), x))}))
export const evenLaws = (r = evens()): Law[] => [r.law('x is even', ({x}) => exists(k => x.eq(k.times(2))))]

export const members = (bug?: 'drops a name') => rule('members').inputs({op: oneOf('add', 'look', 'drop'), name: nat}).state({count: 0}).maps({S: 0})
  .step(({op, name, count, S}) => ({
    S: S.set(name, when(op.is('add'), 1, when(op.is('drop').and(bug ? count.atLeast(0) : count.lt(0)), 0, S.at(name)))),
    count: when(op.is('add'), count.plus(1), count),
  }))
export const memberLaws = (r = members()): Law[] => [r.law('once something was added, some name is in', ({count, S}) => count.atLeast(1).implies(exists(k => S.at(k).eq(1))))]

export const ledger = (bug?: 'charges a fee of 1') => rule('ledger').inputs({amount: int}).ints({balance: 0})
  .assume(({amount}) => exists(int, k => amount.eq(k.times(5))))
  .step(({amount, balance}) => ({balance: balance.plus(amount).minus(bug ? 1 : 0)}))
export const ledgerLaws = (r = ledger()): Law[] => [r.law('the balance is a multiple of 5', ({balance}) => exists(int, j => balance.eq(j.times(5))))]

export const window = () => rule('window').inputs({op: oneOf('extend', 'close'), d: nat}).state({lo: 0, hi: 0})
  .step(({op, d, lo, hi}) => ({hi: when(op.is('extend'), hi.plus(d), hi), lo: when(op.is('close'), hi, lo)}))
export const windowLaws = (r = window(), given?: 'hi + 1'): Law[] => [r.law('some time is in the window', ({lo, hi}) => exists(t => t.atLeast(lo).and(t.atMost(hi)), given ? hi.plus(1) : undefined))]

// The rules with their laws, as the Lean export takes them.
export const leanItems = () => [
  {id: 'evens', machine: evens().machine, laws: evenLaws()},
  {id: 'members', machine: members().machine, laws: memberLaws()},
  {id: 'ledger', machine: ledger().machine, laws: ledgerLaws()},
  {id: 'window', machine: window().machine, laws: windowLaws()},
]

if (import.meta.main) {
  if (process.argv.includes('--lean')) {
    const {toLean} = await import('../lean-kernel/emit.ts')
    console.log(toLean(leanItems(), {title: 'there exists', cyclic: process.argv.includes('cyclic')}))
  } else {
    const say = (what: string, v: ReturnType<typeof proveRule>) => console.log(`${what}: ${v.proven && v.checked ? 'proven' : v.run ? `refuted by a run of ${v.run.trace.length} steps` : `not proven (${v.why ?? v.stuck})`}${v.witnesses ? `, ${Object.values(v.witnesses).join('; ')}` : ''}`)
    const e = evens(), eb = evens('steps by 3'), m = members(), mb = members('drops a name'), l = ledger(), lb = ledger('charges a fee of 1')
    say('evens', proveRule(e, evenLaws(e), {search: false}))
    say('evens, stepping by 3', proveRule(eb, evenLaws(eb), {search: false}))
    say('members', proveRule(m, memberLaws(m), {search: false}))
    say('members, with a drop', proveRule(mb, memberLaws(mb), {search: false}))
    say('ledger', proveRule(l, ledgerLaws(l), {search: false}))
    say('ledger, with a fee', proveRule(lb, ledgerLaws(lb), {search: false}))
    const w = window()
    say('window', proveRule(w, windowLaws(w), {search: false}))
    say('window, the witness hi + 1 given', proveRule(w, windowLaws(w, 'hi + 1'), {search: false}))
  }
}
