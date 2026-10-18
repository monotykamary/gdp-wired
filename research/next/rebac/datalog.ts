// A generic semi-naive Datalog engine, run on the rules exactly as written in model.ts: the reference that the fast
// paths are checked against on small orgs. Relations are sets of tuples; a rule joins its body atoms left to right.
import {GROUPS, type Org} from './model.ts'

type Atom = {rel: string, args: string[]} // args: variables (lowercase) or constants
type Rule = {head: Atom, body: Atom[]}
const rules: Rule[] = [
  {head: {rel: 'member', args: ['u', 'g']}, body: [{rel: 'in', args: ['u', 'g']}]},
  {head: {rel: 'member', args: ['u', 'g']}, body: [{rel: 'member', args: ['u', 'h']}, {rel: 'sub', args: ['h', 'g']}]},
  {head: {rel: 'viewer', args: ['u', 'o']}, body: [{rel: 'grant_user', args: ['u', 'o']}]},
  {head: {rel: 'viewer', args: ['u', 'o']}, body: [{rel: 'member', args: ['u', 'g']}, {rel: 'grant_group', args: ['g', 'o']}]},
  {head: {rel: 'viewer', args: ['u', 'o']}, body: [{rel: 'viewer', args: ['u', 'p']}, {rel: 'parent', args: ['o', 'p']}]},
]

export function evaluate(org: Org): Set<string> {
  const facts = new Map<string, Set<string>>()
  const add = (rel: string, t: number[]) => {
    if (!facts.has(rel)) facts.set(rel, new Set())
    const key = t.join(',')
    if (facts.get(rel)!.has(key)) return false
    facts.get(rel)!.add(key)
    return true
  }
  for (let u = 0; u < org.users; u++) {
    for (let g = 0; g < GROUPS; g++) if ((org.userGroups[u]! >>> g) & 1) add('in', [u, g])
    for (const o of [org.userGrant[2 * u]!, org.userGrant[2 * u + 1]!]) if (o >= 0) add('grant_user', [u, o])
  }
  for (let g = 0; g < GROUPS; g++) for (let h = 0; h < GROUPS; h++) if ((org.sub[g]! >>> h) & 1) add('sub', [g, h])
  for (let o = 0; o < org.objects; o++) {
    if (org.parent[o]! >= 0) add('parent', [o, org.parent[o]!])
    for (let g = 0; g < GROUPS; g++) if ((org.grantGroups[o]! >>> g) & 1) add('grant_group', [g, o])
  }
  // Index each relation by its first column, for joins.
  const tuples = (rel: string) => [...(facts.get(rel) ?? [])].map(k => k.split(',').map(Number))
  for (let changed = true; changed;) {
    changed = false
    for (const rule of rules) {
      let bindings: Record<string, number>[] = [{}]
      for (const atom of rule.body) {
        const ts = tuples(atom.rel)
        bindings = bindings.flatMap(b => ts.flatMap(t => {
          const nb = {...b}
          for (const [i, a] of atom.args.entries()) {
            if (a in nb && nb[a] !== t[i]) return []
            nb[a] = t[i]!
          }
          return [nb]
        }))
      }
      for (const b of bindings) changed = add(rule.head.rel, rule.head.args.map(a => b[a]!)) || changed
    }
  }
  return facts.get('viewer') ?? new Set()
}
