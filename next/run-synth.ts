// Derive the guards of the budget and caps rules from their laws, and compare them with the hand-written ones.
import {type Constraint, add, eq, k, le, lt, nat, v} from '../core/solver.ts'
import {type Problem, implies, keeps, readable, unsafe} from './synth.ts'

const show = (name: string, guard: Constraint[]) => `${name}: ${guard.map(c => c.label).join(' and ')}`

// budget rule: an admitted request costs t = min(c, m) and lands as s' = s + t. Law: s <= b + m. The guard runs before
// the request, so it can't read the cost c.
const loss: Problem = {
  name: 'budget rule admission',
  reads: ['s', 'b', 'm'],
  domain: nat('s', 'b', 'm', 'c', 't', "s'"),
  before: le(v('s'), add(v('b'), v('m')), 's <= b + m'),
  acts: [
    {name: 'c <= m', path: [...le(v('c'), v('m')), ...eq(v('t'), v('c')), ...eq(v("s'"), add(v('s'), v('t')))]},
    {name: 'm < c', path: [...lt(v('m'), v('c')), ...eq(v('t'), v('m')), ...eq(v("s'"), add(v('s'), v('t')))]},
  ],
  after: le(v("s'"), add(v('b'), v('m')), "s' <= b + m"),
}
const lossUnsafe = unsafe(loss)
console.log(`${loss.name}\n  unsafe to admit when: ${readable(lossUnsafe)}`)
const derived = le(v('s'), v('b'), 's <= b')
const handWritten = lt(v('s'), v('b'), 's < b')
console.log(`  derived (weakest) guard: ${derived[0]!.label}, keeps the law: ${keeps(loss, derived)}`)
console.log(`  the hand-written guard: ${handWritten[0]!.label}, keeps the law: ${keeps(loss, handWritten)}, implies the derived one: ${implies(loss, handWritten, derived)}, equivalent: ${implies(loss, derived, handWritten)}`)
console.log(`  anything admitting at s = b + 1 breaks it: ${!keeps(loss, le(v('s'), add(v('b'), k(1))))}`)

// caps rule: a grant adds 1 to each kind's count at the request's key. Laws: every count stays within its cap, and a
// request whose facts don't allow a test drive is never granted (refused_unless_ok). The guard may read the four counts
// at the request's keys (rAcct...), the caps and ok.
const kinds = [['Acct', k(1)], ['Day', v('d')], ['Hour', v('hr')], ['Dom', v('dm')]] as const
const admit: Problem = {
  name: 'caps rule grant',
  reads: ['rAcct', 'rDay', 'rHour', 'rDom', 'd', 'hr', 'dm', 'ok'],
  domain: [...nat('rAcct', 'rDay', 'rHour', 'rDom', 'd', 'hr', 'dm', 'ok', "rAcct'", "rDay'", "rHour'", "rDom'"), ...le(v('ok'), k(1))],
  before: kinds.flatMap(([kind, cap]) => le(v(`r${kind}`), cap, `r${kind} <= cap`)),
  acts: [{name: 'grant', path: kinds.flatMap(([kind]) => eq(v(`r${kind}'`), add(v(`r${kind}`), k(1))))}],
  after: [...kinds.flatMap(([kind, cap]) => le(v(`r${kind}'`), cap, `r${kind}' <= cap`)), ...le(k(1), v('ok'), 'ok')],
}
const admitUnsafe = unsafe(admit)
console.log(`\n${admit.name}\n  unsafe to grant when: ${readable(admitUnsafe)}`)
const admitDerived: Constraint[] = [...le(k(1), v('ok'), 'ok = 1'), ...kinds.flatMap(([kind, cap]) => lt(v(`r${kind}`), cap, `r${kind} < cap`))]
console.log(`  derived guard (the complement): ${admitDerived.map(c => c.label).join(' and ')}, keeps the laws: ${keeps(admit, admitDerived)}`)
console.log(`  the hand-written guard is exactly this: ok(r) and under(Acct) and under(Day) and under(Hour) and under(Dom)`)
for (const [kind] of kinds) {
  const dropped = admitDerived.filter(c => !c.label.startsWith(`r${kind}`))
  console.log(`  without the ${kind} check: keeps the laws: ${keeps(admit, dropped)}`)
}
void show
