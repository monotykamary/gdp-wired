// The access spec's laws (spec.ts, laws.ts) decided by the solver instead of a hand-picked set of worlds: every
// assignment of the 6 atoms is either reachable, with a witness org that the spec's own interpreter confirms, or
// unreachable, with a derivation that core/check.ts verifies. Laws are then read off the reachable assignments.
import {checkRefutation, checkWitness} from '../../core/check.ts'
import {type C, type E, conditionCases, n, x} from '../../core/machine.ts'
import {type Constraint, k, le, nat, solve, v} from '../../core/solver.ts'
import {type Org, evalBool, membershipSlots} from './model.ts'
import {type AtomName, type Bool, type Num, atomNames, atoms, evalFormula, policies} from './spec.ts'

const toE = (num: Num): E => (num.op === 'const' ? n(num.value) : x(num.op))
const toC = (b: Bool): C => {
  switch (b.op) {
    case '>=': return {op: '<=', a: toE(b.b), b: toE(b.a)}
    case '===': return {op: '=', a: toE(b.a), b: toE(b.b)}
    case 'and': case 'or': return {op: b.op, xs: b.xs.map(toC)}
    case 'not': return {op: 'not', x: toC(b.x)}
    case 'atom': throw new Error('atoms only')
  }
}
// What any org's facts satisfy for one (user, project) pair.
const domain: Constraint[] = [...nat('role', 'plan', 'staff', 'sharedDomain'), ...le(v('role'), k(3)), ...le(v('plan'), k(2)), ...le(v('staff'), k(1)), ...le(k(1), v('userDomain'))]
const orgOf = (w: Record<string, number>): Org => {
  const memberTeam = new Int32Array(membershipSlots).fill(-1), memberRole = new Uint8Array(membershipSlots)
  if (w.role! > 0) [memberTeam[0], memberRole[0]] = [0, w.role!]
  const domains = Math.max(w.userDomain!, w.sharedDomain!, 1)
  return {users: 1, teams: 1, projects: 1, domains, memberTeam, memberRole, staff: Uint8Array.of(w.staff!), userDomain: Int32Array.of(w.userDomain!),
    plan: Uint8Array.of(w.plan!), teamOf: Int32Array.of(0), sharedDomain: Int32Array.of(w.sharedDomain!)}
}

const reachable: number[] = []
let certified = 0, derivationSteps = 0, failures = 0
for (let index = 0; index < 1 << atomNames.length; index++) {
  const truth = (name: AtomName) => ((index >> atomNames.indexOf(name)) & 1) === 1
  let combos: Constraint[][] = [domain]
  for (const name of atomNames) combos = combos.flatMap(cs => conditionCases(toC(atoms[name].expr), truth(name)).map(c => [...cs, ...c]))
  let witness: Record<string, number> | undefined
  const refutations: boolean[] = []
  for (const cs of combos) {
    const verdict = solve(cs)
    if (verdict.kind === 'sat' && checkWitness(cs, verdict.witness)) witness ??= verdict.witness
    else if (verdict.kind === 'refuted') (refutations.push(checkRefutation(cs, verdict.steps)), derivationSteps += verdict.steps.length)
    else refutations.push(false)
  }
  if (witness) {
    // The witness as a real org, through the spec's own interpreter: it must give exactly this assignment.
    const org = orgOf(witness)
    if (!atomNames.every(name => evalBool(org, atoms[name].expr, 0, 0) === truth(name))) failures++
    reachable.push(index)
  } else if (refutations.every(Boolean)) certified++
  else failures++
}
console.log(`${reachable.length} reachable assignments, each with a witness org the interpreter confirms; ${certified} unreachable, each refuted (${derivationSteps} checked derivation steps); ${failures} failures`)

const value = (index: number) => (name: AtomName) => ((index >> atomNames.indexOf(name)) & 1) === 1
const laws: [string, (a: (n: AtomName) => boolean, p: (n: keyof typeof policies) => boolean) => boolean][] = [
  ['whoever may set protection may see it', (_, p) => !p('canSetProtection') || p('canViewProtection')],
  ['the proposal keeps every team member', (a, p) => !a('UserHasProjectAccess') || p('canViewProtectionProposed')],
  ['the proposal removes no one', (_, p) => !p('canViewProtection') || p('canViewProtectionProposed')],
]
for (const [name, holds] of laws) {
  const broken = reachable.find(i => !holds(value(i), policy => evalFormula(policies[policy], value(i))))
  console.log(broken === undefined ? `  PROVEN   ${name}` : `  REFUTED  ${name}: ${atomNames.filter(a => value(broken)(a)).join(' & ') || 'no atom'}`)
}
