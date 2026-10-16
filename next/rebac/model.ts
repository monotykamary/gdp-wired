// A Zanzibar-style org: users in groups, groups nested in groups, folders in a tree, grants of view to a group or a
// user on a folder, inherited by everything under it. The rules, as Datalog:
//   member(u, g)  :- in(u, g).
//   member(u, g)  :- member(u, h), sub(h, g).          h is nested in g
//   viewer(u, o)  :- grant_user(u, o).
//   viewer(u, o)  :- member(u, g), grant_group(g, o).
//   viewer(u, o)  :- viewer(u, p), parent(o, p).       a folder's viewers see what's under it
// No rule negates, so adding a fact never removes a viewer, and inheritance holds by the last rule.

export const GROUPS = 32
export type Org = {
  users: number, objects: number
  userGroups: Uint32Array // users: bit g when in(u, g)
  userGrant: Int32Array // users × 2: objects granted to the user directly, -1 for none
  parent: Int32Array // objects: parent, -1 for a root
  grantGroups: Uint32Array // objects: bit g when grant_group(g, o)
  sub: Uint32Array // groups: bit h when sub(g, h), i.e. g is nested in h
  finance: number // the root of /finance
  financeGroup: number // group 0, Finance
}

function random(seed: number) {
  let state = seed >>> 0
  return () => {
    state = (state + 0x6d2b79f5) >>> 0
    let t = Math.imul(state ^ (state >>> 15), state | 1)
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61)
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296
  }
}

// `stray`: one grant that breaks the finance law, to see the audit find it.
export function generate(users: number, objects: number, stray: boolean, seed = 3): Org {
  const next = random(seed)
  const pick = (n: number) => Math.floor(next() * n)
  // Folders: object 0 is the root, 1 is /finance; each other object's parent is an earlier object, depth <= 8.
  const parent = new Int32Array(objects).fill(-1), depth = new Int32Array(objects)
  for (let o = 1; o < objects; o++) {
    let p = o === 1 ? 0 : pick(o)
    while (depth[p]! >= 7) p = parent[p]!
    parent[o] = p
    depth[o] = depth[p]! + 1
  }
  // Groups: 0 Finance, 1 Finance leads (nested in Finance), 2 Contractors; others nest into lower-numbered groups.
  const sub = new Uint32Array(GROUPS)
  sub[1] = 1 << 0
  for (let g = 3; g < GROUPS; g++) if (next() < 0.5) sub[g] = (1 << (3 + pick(g - 3))) >>> 0
  // Grants: Finance on /finance; each other folder outside /finance gets a group grant with some probability.
  const under = (o: number, root: number) => { for (let a = o; a >= 0; a = parent[a]!) if (a === root) return true; return false }
  const grantGroups = new Uint32Array(objects)
  grantGroups[1] = 1 << 0
  for (let o = 2; o < objects; o++) if (!under(o, 1) && next() < 0.05) grantGroups[o] = (grantGroups[o]! | (1 << (2 + pick(GROUPS - 2)))) >>> 0
  if (stray) {
    const inFinance = [...Array(objects).keys()].filter(o => o > 1 && under(o, 1))
    grantGroups[inFinance[0]!] = (grantGroups[inFinance[0]!]! | (1 << 2)) >>> 0 // Contractors on a finance folder
  }
  const userGroups = new Uint32Array(users).map(() => {
    let bits = 0
    for (let i = 0; i < 1 + pick(3); i++) bits |= 1 << (next() < 0.03 ? pick(2) : 2 + pick(GROUPS - 2))
    return bits >>> 0
  })
  const userGrant = new Int32Array(users * 2).fill(-1)
  for (let u = 0; u < users; u++) if (next() < 0.02) userGrant[2 * u] = 2 + pick(objects - 2)
  // A direct user grant inside /finance only for Finance members.
  for (let u = 0; u < users; u++) if (userGrant[2 * u]! >= 0 && under(userGrant[2 * u]!, 1) && !(userGroups[u]! & 3)) userGrant[2 * u] = -1
  return {users, objects, userGroups, userGrant, parent, grantGroups, sub, finance: 1, financeGroup: 0}
}

// Object-side tables the fast paths share: the groups granted on an object or any ancestor, the Euler interval of
// each object (descendant test in O(1)), and whether it lies under /finance.
export function derive(org: Org) {
  const {objects, parent, grantGroups} = org
  const inherited = new Uint32Array(objects), tin = new Int32Array(objects), tout = new Int32Array(objects), underFinance = new Uint32Array(objects)
  const children: number[][] = Array.from({length: objects}, () => [])
  for (let o = 1; o < objects; o++) children[parent[o]!]!.push(o)
  let clock = 0
  const walk = (o: number, above: number, fin: boolean) => {
    inherited[o] = (above | grantGroups[o]!) >>> 0
    underFinance[o] = fin || o === org.finance ? 1 : 0
    tin[o] = clock++
    for (const c of children[o]!) walk(c, inherited[o]!, underFinance[o] === 1)
    tout[o] = clock - 1
  }
  walk(0, 0, false)
  return {inherited, tin, tout, underFinance}
}

// member(u, ·) as a bitset: the closure of the user's groups under nesting, 4 rounds (nesting depth <= 4 here; the
// generator only nests groups into lower-numbered ones, so it is acyclic).
export function closure(groups: number, sub: Uint32Array): number {
  for (let round = 0; round < 5; round++) {
    let next = groups
    for (let g = 0; g < GROUPS; g++) if ((groups >>> g) & 1) next |= sub[g]!
    next >>>= 0
    if (next === groups) break
    groups = next
  }
  return groups
}
