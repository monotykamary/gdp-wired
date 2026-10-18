// An org's facts as typed arrays, shaped like examples/basic/src/db.ts at scale: teams with a plan, users with up to
// four team memberships, projects owned by a team and optionally shared with an email domain.
import {type Bool, type Num, Plan, Role} from './spec.ts'

export const membershipSlots = 4

export type Sizes = {users: number, teams: number, projects: number, domains: number}

export type Org = Sizes & {
  memberTeam: Int32Array // users × 4, -1 for an empty slot; a user's teams are distinct
  memberRole: Uint8Array // users × 4, 1..3
  staff: Uint8Array // users
  userDomain: Int32Array // users, 1..domains
  plan: Uint8Array // teams
  teamOf: Int32Array // projects
  sharedDomain: Int32Array // projects, 0 when not shared
}

function random(seed: number) {
  let state = seed >>> 0
  return () => {
    state = (state + 0x6d2b79f5) >>> 0
    let t = state
    t = Math.imul(t ^ (t >>> 15), t | 1)
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61)
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296
  }
}

export function generateOrg(sizes: Sizes, seed = 1): Org {
  const next = random(seed)
  const pick = (count: number) => Math.floor(next() * count)
  const {users, teams, projects, domains} = sizes
  const plan = new Uint8Array(teams).map(() => {
    const r = next()
    return r < 0.6 ? Plan.hobby : r < 0.9 ? Plan.pro : Plan.enterprise
  })
  const memberTeam = new Int32Array(users * membershipSlots).fill(-1)
  const memberRole = new Uint8Array(users * membershipSlots)
  for (let user = 0; user < users; user++) {
    const count = 1 + pick(membershipSlots)
    for (let slot = 0; slot < count; slot++) {
      let team = pick(teams)
      while ([...memberTeam.subarray(user * membershipSlots, user * membershipSlots + slot)].includes(team)) team = pick(teams)
      memberTeam[user * membershipSlots + slot] = team
      memberRole[user * membershipSlots + slot] = [Role.viewer, Role.member, Role.owner][pick(3)]!
    }
  }
  const staff = new Uint8Array(users).map(() => (next() < 0.01 ? 1 : 0))
  const userDomain = new Int32Array(users).map(() => 1 + pick(domains))
  const teamOf = new Int32Array(projects).map(() => pick(teams))
  const sharedDomain = new Int32Array(projects).map(() => (next() < 0.05 ? 1 + pick(domains) : 0))
  return {...sizes, memberTeam, memberRole, staff, userDomain, plan, teamOf, sharedDomain}
}

// The facts' numbers for one pair, by the expression language's own definitions.
export function readNum(org: Org, num: Num, user: number, project: number): number {
  switch (num.op) {
    case 'const': return num.value
    case 'role': {
      const team = org.teamOf[project]!
      for (let slot = 0; slot < membershipSlots; slot++) {
        if (org.memberTeam[user * membershipSlots + slot] === team) return org.memberRole[user * membershipSlots + slot]!
      }
      return Role.none
    }
    case 'plan': return org.plan[org.teamOf[project]!]!
    case 'staff': return org.staff[user]!
    case 'userDomain': return org.userDomain[user]!
    case 'sharedDomain': return org.sharedDomain[project]!
  }
}

// The interpreter: what a predicate means. gdp.ts mints proofs with it, and check.ts compares everything with it.
export function evalBool(org: Org, expr: Bool, user: number, project: number): boolean {
  switch (expr.op) {
    case '>=': return readNum(org, expr.a, user, project) >= readNum(org, expr.b, user, project)
    case '===': return readNum(org, expr.a, user, project) === readNum(org, expr.b, user, project)
    case 'and': return expr.xs.every(x => evalBool(org, x, user, project))
    case 'or': return expr.xs.some(x => evalBool(org, x, user, project))
    case 'not': return !evalBool(org, expr.x, user, project)
    case 'atom': throw new Error('a predicate reads facts, not other predicates')
  }
}
