// The one source. Each trusted predicate of the gdp-ts example (examples/basic/src/proofs) is written once, as an
// expression over an org's facts, and each policy as a formula over those predicates. gdp.ts turns the predicates into
// gdp-ts provers that mint proofs one request at a time; circuit.ts turns the same expressions into a Handwired loop
// program that decides every (user, project) pair at once.

export const Role = {none: 0, viewer: 1, member: 2, owner: 3} as const
export const Plan = {hobby: 0, pro: 1, enterprise: 2} as const

import {unreachable} from '../../core/machine.ts'

// A number read from the facts about one (user, project) pair.
export type Num =
  | {op: 'role'} // the user's role in the team that owns the project, 0 when none
  | {op: 'plan'} // the plan of the team that owns the project
  | {op: 'staff'} // 1 when the user is support staff
  | {op: 'userDomain'} // the user's email domain, 1..D
  | {op: 'sharedDomain'} // the email domain the project is shared with, 0 when none
  | {op: 'const', value: number}

export type Bool =
  | {op: '>=' | '===', a: Num, b: Num}
  | {op: 'and' | 'or', xs: Bool[]}
  | {op: 'not', x: Bool}
  | {op: 'atom', name: AtomName}

const n = (value: number): Num => ({op: 'const', value})
const read = (op: Exclude<Num['op'], 'const'>) => ({op}) as Num

export const atoms = {
  // examples/basic: `role === "owner" || role === "member"`
  UserIsProjectAdmin: {about: 'pair', expr: {op: '>=', a: read('role'), b: n(Role.member)}},
  // examples/basic: `role ? ... : null`
  UserHasProjectAccess: {about: 'pair', expr: {op: '>=', a: read('role'), b: n(Role.viewer)}},
  // examples/basic: `plan === "pro" || plan === "enterprise"`
  PlanIncludesPasswordProtection: {about: 'project', expr: {op: '>=', a: read('plan'), b: n(Plan.pro)}},
  // Added here, so that a policy can reach outside the user's own teams.
  PlanIsEnterprise: {about: 'project', expr: {op: '===', a: read('plan'), b: n(Plan.enterprise)}},
  UserIsSupportStaff: {about: 'user', expr: {op: '===', a: read('staff'), b: n(1)}},
  ProjectSharedWithUserDomain: {about: 'pair', expr: {op: '===', a: read('sharedDomain'), b: read('userDomain')}},
} as const satisfies Record<string, {about: 'pair' | 'user' | 'project', expr: Bool}>

export type AtomName = keyof typeof atoms
export const atomNames = Object.keys(atoms) as AtomName[]

const atom = (name: AtomName): Bool => ({op: 'atom', name})
const or = (...xs: Bool[]): Bool => ({op: 'or', xs})
const and = (...xs: Bool[]): Bool => ({op: 'and', xs})

// Policies are unions of proofs, as in examples/basic/src/proofs/protection-policy.ts.
export const policies = {
  // Today: the team, support staff on enterprise teams, and anyone at a domain the project is shared with.
  canViewProtection: or(
    atom('UserIsProjectAdmin'),
    atom('UserHasProjectAccess'),
    and(atom('UserIsSupportStaff'), atom('PlanIsEnterprise')),
    atom('ProjectSharedWithUserDomain'),
  ),
  // A proposed change: sharing with a domain needs a paid plan, and support staff also see pro teams.
  canViewProtectionProposed: or(
    atom('UserIsProjectAdmin'),
    atom('UserHasProjectAccess'),
    and(atom('UserIsSupportStaff'), atom('PlanIncludesPasswordProtection')),
    and(atom('ProjectSharedWithUserDomain'), atom('PlanIncludesPasswordProtection')),
  ),
  // examples/basic/src/data.ts: setPasswordProtection takes {manage, plan}.
  canSetProtection: and(atom('UserIsProjectAdmin'), atom('PlanIncludesPasswordProtection')),
} satisfies Record<string, Bool>

export type PolicyName = keyof typeof policies

// A policy as data: its value at every assignment of the atoms, indexed by sum of bit_i × 2^i in atomNames' order.
// A circuit reads it with one table read, so a new policy writes 64 cells and changes no program.
export function truthTable(policy: Bool): Uint8Array {
  const table = new Uint8Array(1 << atomNames.length)
  for (let index = 0; index < table.length; index++) {
    const value = (name: AtomName) => ((index >> atomNames.indexOf(name)) & 1) === 1
    table[index] = evalFormula(policy, value) ? 1 : 0
  }
  return table
}

export function evalFormula(formula: Bool, atomValue: (name: AtomName) => boolean): boolean {
  switch (formula.op) {
    case 'atom': return atomValue(formula.name)
    case 'and': return formula.xs.every(x => evalFormula(x, atomValue))
    case 'or': return formula.xs.some(x => evalFormula(x, atomValue))
    case 'not': return !evalFormula(formula.x, atomValue)
    case '>=': case '===': throw new Error(`a policy combines atoms, not ${formula.op}`)
    default: return unreachable(formula)
  }
}
