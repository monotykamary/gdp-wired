// Laws about policies, decided rather than tested. An atom only compares the facts of one pair with each other and
// with constants, so a small set of values that covers every constant and every equal/unequal case reaches every
// assignment of the atoms that any org can reach (a small model). Enumerating those worlds decides a law for every
// org of any size. The same worlds also check that the circuit computes the spec on every reachable case.
// Usage: bun laws.ts
import {createLoopRunner} from './vendor/handwired/src/json-search/loop-program.ts'
import {buildAudit, writeUserCells} from './circuit.ts'
import {type Org, evalBool, membershipSlots} from './model.ts'
import {type AtomName, type Bool, atomNames, atoms, evalFormula, policies, type PolicyName, truthTable} from './spec.ts'

type Law = {name: string, holds: (value: (name: AtomName) => boolean, policy: (name: PolicyName) => boolean) => boolean}
const implies = (a: boolean, b: boolean) => !a || b

const laws: Law[] = [
  {name: 'whoever may set protection may see it', holds: (_, p) => implies(p('canSetProtection'), p('canViewProtection'))},
  {name: 'setting protection needs a paid plan', holds: (a, p) => implies(p('canSetProtection'), a('PlanIncludesPasswordProtection'))},
  {name: 'the proposal keeps every team member', holds: (a, p) => implies(a('UserHasProjectAccess'), p('canViewProtectionProposed'))},
  {name: 'the proposal removes no one', holds: (_, p) => implies(p('canViewProtection'), p('canViewProtectionProposed'))},
  {name: 'outsiders never see a hobby project', holds: (a, p) => implies(!a('UserHasProjectAccess') && !a('PlanIncludesPasswordProtection'), !p('canViewProtectionProposed'))},
]

// One org of one user and one project per world: every role, plan, staff bit and domain relation.
type World = {role: number, plan: number, staff: number, userDomain: number, sharedDomain: number}
const worlds: World[] = []
for (const role of [0, 1, 2, 3]) for (const plan of [0, 1, 2]) for (const staff of [0, 1])
  for (const userDomain of [1, 2]) for (const sharedDomain of [0, 1, 2]) worlds.push({role, plan, staff, userDomain, sharedDomain})

const orgOf = (w: World): Org => {
  const memberTeam = new Int32Array(membershipSlots).fill(-1)
  const memberRole = new Uint8Array(membershipSlots)
  if (w.role > 0) {
    memberTeam[0] = 0
    memberRole[0] = w.role
  }
  return {users: 1, teams: 1, projects: 1, domains: 2, memberTeam, memberRole, staff: Uint8Array.of(w.staff), userDomain: Int32Array.of(w.userDomain),
    plan: Uint8Array.of(w.plan), teamOf: Int32Array.of(0), sharedDomain: Int32Array.of(w.sharedDomain)}
}

const reached = new Set<number>()
const counterexamples = new Map<string, World>()
const built = buildAudit({projects: 1, teams: 1, domains: 2})
const runner = createLoopRunner(built.loop, 'generated')
const tableOf = (name: PolicyName) => truthTable(policies[name] as Bool)
let circuitMismatches = 0
for (const world of worlds) {
  const org = orgOf(world)
  const atom = (name: AtomName) => evalBool(org, atoms[name].expr, 0, 0)
  const policy = (name: PolicyName) => evalFormula(policies[name], atom)
  reached.add(atomNames.reduce((sum, name, bit) => sum + (atom(name) ? 1 << bit : 0), 0))
  for (const law of laws) if (!law.holds(atom, policy) && !counterexamples.has(law.name)) counterexamples.set(law.name, world)
  // The circuit on this world, for every pair of policies: its code is A + 2B.
  for (const a of Object.keys(policies) as PolicyName[]) for (const b of Object.keys(policies) as PolicyName[]) {
    const shared = new Float32Array(built.loop.sharedValues)
    built.writeShared(shared, org, tableOf(a), tableOf(b))
    runner.setShared(shared)
    const outputs = [new Float32Array(4), new Float32Array(1)]
    runner.run([writeUserCells(org)], 0, outputs, 0, 0)
    if (outputs[1]![0] !== +policy(a) + 2 * +policy(b)) circuitMismatches++
  }
}

console.log(`${worlds.length} worlds reach ${reached.size} of ${1 << atomNames.length} assignments of the ${atomNames.length} atoms`)
for (const law of laws) {
  const world = counterexamples.get(law.name)
  console.log(world === undefined ? `  PROVEN   ${law.name}` : `  REFUTED  ${law.name}: ${JSON.stringify(world)}`)
}
console.log(circuitMismatches === 0 ? 'the circuit computes every policy on every world' : `${circuitMismatches} circuit mismatches`)
