// Untrusted strengthening proposals for an ordered pair of rows with a shared group key.
// A successful search must check the original law and this whole family against the same machine.
import { all, any, not, same, x, get, n, type C, type E, type Law, type Machine } from './machine.ts'

const isVar = (t: E, k: string) => t.op === 'var' && t.name === k
const rowRead = (t: E, k: string): string | undefined => t.op === 'get' && isVar(t.key, k) ? t.map : undefined
const conjuncts = (c: C): C[] => c.op === 'and' ? c.xs.flatMap(conjuncts) : [c]
const forbidden = (c: C): C[] | undefined => {
  if (c.op === 'not') return conjuncts(c.x)
  if (c.op === 'or' && c.xs.every(p => p.op === 'not')) return c.xs.flatMap(p => conjuncts(p.x))
  return undefined
}
const pairGroup = (c: C, i: string, j: string): string | undefined => {
  if (c.op !== '=') return
  const lr = (a: E, b: E) => { const m = rowRead(a, i); return m && m === rowRead(b, j) ? m : undefined }
  return lr(c.a, c.b) ?? lr(c.b, c.a)
}
const rowTest = (c: C, k: string): { map: string, value: number, positive: boolean } | undefined => {
  const e = c.op === 'not' ? c.x : c
  if (e.op !== '=') return
  const test = (a: E, b: E) => { const map = rowRead(a,k); return map && b.op === 'const' ? { map, value: b.value, positive: c.op !== 'not' } : undefined }
  return test(e.a,e.b) ?? test(e.b,e.a)
}
function canAssign(value: E, tag: number): boolean {
  const seen = new Set<E>(), stack = [value]
  while (stack.length && seen.size < 2048) {
    const e = stack.pop()!
    if (seen.has(e)) continue
    seen.add(e)
    if (e.op === 'const' && e.value === tag) return true
    if (e.op === 'if') stack.push(e.then, e.else)
  }
  return false
}

// A none-branch of a row selection can rule out old rows in the same group. Read only a
// simple one-tag absence query; maxima, grouped disjunctions and join predicates aren't tags.
function selectedTags(m: Machine, group: string, tagMap: string): number[] {
  const tags = new Set<number>()
  for (const flag of Object.values(m.step.flags ?? {})) {
    if (flag.op !== 'all' || flag.keys?.length || flag.finite) continue
    const cs = forbidden(flag.c)
    if (!cs) continue
    const k = flag.key
    const sameGroup = cs.some(c => c.op === '=' && [[c.a,c.b],[c.b,c.a]].some(([a,b]) =>
      a && b && rowRead(a,k) === group && b.op === 'var' && m.inputs.includes(b.name)))
    const tests = cs.map(c => rowTest(c, k)).filter(t => t?.map === tagMap && t.positive)
    if (sameGroup && tests.length === 1) tags.add(tests[0]!.value)
  }
  return [...tags]
}

// Project the later row to its tag, and project negative row filters out of the
// earlier row. Close the projected pattern under retagging from an exclusive
// selector: the old selected tag can precede neither a target nor another
// selected tag. Infer the coordinates and values from the law, writes and
// quantified row-selection guards. This deliberately small grammar can miss
// invariants or propose false ones; neither case can authorize a verdict.
export function orderedPairSeed(m: Machine, law: Law): Law | undefined {
  const i = law.forall, j = law.keys?.[0]
  if (!i || !j || law.keys?.length !== 1 || law.some?.length || law.finite || i === j) return
  const cs = forbidden(law.holds)
  if (!cs || cs.length > 16) return
  const groups = cs.map(c => pairGroup(c,i,j)).filter(g => g !== undefined)
  if (groups.length !== 1 || !Object.hasOwn(m.maps ?? {}, groups[0]!)) return
  const group = groups[0]!
  const frame: C[] = [], left: NonNullable<ReturnType<typeof rowTest>>[] = [], right: typeof left = []
  for (const c of cs) {
    const l = rowTest(c,i), r = rowTest(c,j)
    if (l) left.push(l)
    else if (r) right.push(r)
    else if (pairGroup(c,i,j) === group || (c.op === '<' && isVar(c.a,i) && isVar(c.b,j)) ||
      ((c.op === '<' || c.op === '<=') && (isVar(c.a,i) || isVar(c.a,j)) && c.b.op === 'var' && Object.hasOwn(m.state,c.b.name))) frame.push(c)
    else return
  }
  if (!frame.some(c => c.op === '<' && isVar(c.a,i) && isVar(c.b,j))) return
  const ordered = (tests: typeof left) => tests.map(t => JSON.stringify([t.map,t.value,t.positive])).sort().join(';')
  if (ordered(left) !== ordered(right) || left.some(t => !Object.hasOwn(m.maps ?? {},t.map))) return
  const tagOf = left.flatMap(t => {
    const write = Object.hasOwn(m.step.maps ?? {},t.map) ? m.step.maps![t.map] : undefined
    if (!t.positive || !write || !canAssign(write.value,t.value)) return []
    const prior = selectedTags(m,group,t.map).filter(value => value !== t.value)
    return prior.length === 1 ? [{ tag: t, prior: prior[0]! }] : []
  })
  if (tagOf.length !== 1) return
  const {tag,prior} = tagOf[0]!
  const is = (k: string, map: string, value: number) => same(get(map,x(k)),n(value))
  const earlier = all(...left.filter(t => t.positive).map(t => is(i,t.map,t.value)))
  const target = is(j,tag.map,tag.value)
  const blocked = any(all(earlier,target), all(is(i,tag.map,prior),any(is(j,tag.map,prior),target)))
  return {name: `${law.name} [ordered row pairs]`, forall: i, keys: [j], holds: any(not(all(...frame)),not(blocked))}
}
