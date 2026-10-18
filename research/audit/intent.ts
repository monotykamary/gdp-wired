// Laws as the intent, policies as the implementation, and the difference between them, over laws.ts's small model.
// In every reachable world, the laws are constraints on the policies' values. Per world and policy:
//   violated      the policy's value breaks a law
//   determined    the laws allow exactly one value, and the policy has it
//   undetermined  the laws allow both values: the policy made a choice that no law states
//   contradictory the laws allow neither value: the intent itself is inconsistent
// and per law: vacuous when it holds whatever the policies say, i.e. it constrains nothing.
// Then every pair of a generated org is counted by the kind of world it falls in.
// Usage: bun intent.ts
import {type Org, evalBool, generateOrg, membershipSlots} from './model.ts'
import {type AtomName, atomNames, atoms, evalFormula, policies} from './spec.ts'

type Policy = 'view' | 'set'
const implementation: Record<Policy, keyof typeof policies> = {view: 'canViewProtectionProposed', set: 'canSetProtection'}
type Law = {name: string, holds: (a: (name: AtomName) => boolean, p: (name: Policy) => boolean) => boolean}
const implies = (x: boolean, y: boolean) => !x || y

// What we had in mind, written as laws, before looking at the policy.
const intent: Law[] = [
  {name: 'team members see protection', holds: (a, p) => implies(a('UserHasProjectAccess'), p('view'))},
  {name: 'support staff see paid projects', holds: (a, p) => implies(a('UserIsSupportStaff') && a('PlanIncludesPasswordProtection'), p('view'))},
  {name: 'a shared domain sees paid projects', holds: (a, p) => implies(a('ProjectSharedWithUserDomain') && a('PlanIncludesPasswordProtection'), p('view'))},
  {name: 'outsiders never see hobby projects', holds: (a, p) => implies(!a('UserHasProjectAccess') && !a('PlanIncludesPasswordProtection'), !p('view'))},
  {name: 'only admins set protection', holds: (a, p) => implies(p('set'), a('UserIsProjectAdmin'))},
  {name: 'setting needs a paid plan', holds: (a, p) => implies(p('set'), a('PlanIncludesPasswordProtection'))},
  {name: 'admins on paid plans set protection', holds: (a, p) => implies(a('UserIsProjectAdmin') && a('PlanIncludesPasswordProtection'), p('set'))},
  {name: 'whoever sets protection sees it', holds: (_, p) => implies(p('set'), p('view'))},
  {name: 'viewers who are admins without access are refused', holds: (a, p) => implies(a('UserIsProjectAdmin') && !a('UserHasProjectAccess'), !p('view'))},
]

// laws.ts's worlds: one user and one project, every role, plan, staff bit and domain relation.
type World = {role: number, plan: number, staff: number, userDomain: number, sharedDomain: number}
const worlds: World[] = []
for (const role of [0, 1, 2, 3]) for (const plan of [0, 1, 2]) for (const staff of [0, 1])
  for (const userDomain of [1, 2]) for (const sharedDomain of [0, 1, 2]) worlds.push({role, plan, staff, userDomain, sharedDomain})
const orgOf = (w: World): Org => {
  const memberTeam = new Int32Array(membershipSlots).fill(-1)
  const memberRole = new Uint8Array(membershipSlots)
  if (w.role > 0) [memberTeam[0], memberRole[0]] = [0, w.role]
  return {users: 1, teams: 1, projects: 1, domains: 2, memberTeam, memberRole, staff: Uint8Array.of(w.staff), userDomain: Int32Array.of(w.userDomain),
    plan: Uint8Array.of(w.plan), teamOf: Int32Array.of(0), sharedDomain: Int32Array.of(w.sharedDomain)}
}
const indexOf = (atom: (name: AtomName) => boolean) => atomNames.reduce((sum, name, bit) => sum + (atom(name) ? 1 << bit : 0), 0)
const describe = (index: number) => atomNames.filter((_, bit) => (index >> bit) & 1).join(' & ') || 'no atom holds'

// One verdict per reachable atom assignment, since a policy reads only the atoms.
type Verdict = 'violated' | 'determined' | 'undetermined' | 'contradictory'
const verdicts = new Map<number, Record<Policy, {verdict: Verdict, chose: boolean, broken: string[]}>>()
const constraining = new Set<string>()
for (const world of worlds) {
  const org = orgOf(world)
  const atom = (name: AtomName) => evalBool(org, atoms[name].expr, 0, 0)
  const index = indexOf(atom)
  if (verdicts.has(index)) continue
  const actual = (name: Policy) => evalFormula(policies[implementation[name]], atom)
  // Every assignment of the two policies that the laws allow in this world.
  const allowed: Record<Policy, boolean>[] = []
  for (const view of [false, true]) for (const set of [false, true]) {
    const values = {view, set}
    const ok = intent.every(law => law.holds(atom, name => values[name]))
    if (ok) allowed.push(values)
    for (const law of intent) if (!law.holds(atom, name => values[name])) constraining.add(law.name)
  }
  const entry = {} as Record<Policy, {verdict: Verdict, chose: boolean, broken: string[]}>
  for (const policy of ['view', 'set'] as Policy[]) {
    const chose = actual(policy)
    const options = new Set(allowed.map(values => values[policy]))
    const broken = intent.filter(law => !law.holds(atom, actual)).map(law => law.name)
    entry[policy] = {
      chose, broken,
      verdict: options.size === 0 ? 'contradictory' : broken.length > 0 ? 'violated' : options.size === 1 ? 'determined' : 'undetermined',
    }
  }
  verdicts.set(index, entry)
}

console.log(`${verdicts.size} reachable situations (atom assignments) of ${1 << atomNames.length}`)
for (const policy of ['view', 'set'] as Policy[]) {
  const by = (verdict: Verdict) => [...verdicts].filter(([, entry]) => entry[policy].verdict === verdict)
  console.log(`\n${implementation[policy]}: ${by('determined').length} determined by the laws, ${by('undetermined').length} undetermined, ${by('violated').length} violated, ${by('contradictory').length} contradictory`)
  for (const [index, entry] of by('violated')) console.log(`  VIOLATED      ${describe(index)}: chose ${entry[policy].chose ? 'allow' : 'deny'}, breaks "${entry[policy].broken.join('", "')}"`)
  for (const [index, entry] of by('undetermined')) console.log(`  UNDETERMINED  ${describe(index)}: no law says, the policy chose ${entry[policy].chose ? 'allow' : 'deny'}`)
}
const vacuous = intent.filter(law => !constraining.has(law.name))
console.log(`\nvacuous laws (hold in every reachable world whatever the policies say): ${vacuous.map(law => `"${law.name}"`).join(', ') || 'none'}`)

// How much of a real org each kind of situation covers.
const org = generateOrg({users: 2000, teams: 200, projects: 512, domains: 50})
const pairs = new Map<number, number>()
for (let user = 0; user < org.users; user++) for (let project = 0; project < org.projects; project++) {
  const index = indexOf(name => evalBool(org, atoms[name].expr, user, project))
  pairs.set(index, (pairs.get(index) ?? 0) + 1)
}
for (const policy of ['view', 'set'] as Policy[]) {
  const total = (verdict: Verdict) => [...pairs].filter(([index]) => verdicts.get(index)?.[policy].verdict === verdict).reduce((sum, [, count]) => sum + count, 0)
  console.log(`${implementation[policy]} in a 2,000 × 512 org: ${total('determined')} pairs decided by a law, ${total('undetermined')} by a choice no law states, ${total('violated')} against a law`)
}
