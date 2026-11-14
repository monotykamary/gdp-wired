// Isolated MLDR-style region algebra: arbitrary X,S over one finite domain.
// Coefficients are read from partition expressions; the ordinary search finds
// all proof trees. No region equation is admitted as a trusted hypothesis.
import {type C, type E, all, atMost, get, ite, minus, n, not, plus, same, x} from '../core/machine.ts'
import {type Count, type CountedGoal, type CountInst, checkCounted, countedGoal, linear} from '../kernel/kernel.ts'
import {clock, grow} from '../kernel/prove.ts'

export function boundedRegions() {
  const X = same(get('X', x('k')), n(1)), S = same(get('S', x('k')), n(1)), size = x('size')
  const body: Record<string, C> = {xCount: X, sCount: S, xAndS: all(X, S), xNotS: all(X, not(S)), sNotX: all(S, not(X))}
  const counts: Count[] = Object.entries(body).map(([v, c]) => ({v, key: 'k', below: size, body: ite(c, n(1), n(0))}))
  const left = plus(x('xAndS'), x('xNotS')), right = plus(x('xAndS'), x('sNotX'))
  const union = plus(left, x('sNotX'))
  const expressions: [E, E][] = [[x('xCount'), left], [x('sCount'), right], [union, size]]
  const insts: CountInst[] = []
  for (const [index, [a, b]] of expressions.entries()) {
    const la = linear(a, new Map())!, lb = linear(b, new Map())!, delta: Record<string, number> = {...la}
    for (const [v, z] of Object.entries(lb)) delta[v] = (delta[v] ?? 0) - z
    for (const sign of index === 2 ? [1] : [1, -1]) insts.push({
      wit: `region$${insts.length}`, below: size,
      terms: counts.flatMap(c => delta[c.v] ? [[sign * delta[c.v]!, c.v] as [number, string]] : []),
      unit: sign * (delta.size ?? 0),
    })
  }
  const claims: [string, C][] = [
    ['x_partition', same(x('xCount'), left)],
    ['s_partition', same(x('sCount'), right)],
    ['xNotS_difference', same(x('xNotS'), minus(x('xCount'), x('xAndS')))],
    ['sNotX_difference', same(x('sNotX'), minus(x('sCount'), x('xAndS')))],
    ['intersection_bound', all(atMost(x('xAndS'), x('xCount')), atMost(x('xAndS'), x('sCount')))],
    ['union_bound', atMost(union, size)],
  ]
  return claims.map(([id, claim]) => {
    const goal: CountedGoal = {name: id, counts, hyps: [not(claim)]}, plain = countedGoal(goal, insts)
    if (!plain) throw new Error(`${id}: count instances malformed`)
    const out = grow(plain, new Map(), {nodes: 0, until: clock() + 5_000})
    if (!('tree' in out)) throw new Error(`${id}: search did not produce a proof`)
    const certificate = {insts, tree: out.tree}
    if (!checkCounted(goal, certificate)) throw new Error(`${id}: certificate refused`)
    // Dropping every count premise must invalidate the actual certificate.
    if (checkCounted(goal, {...certificate, insts: []})) throw new Error(`${id}: unexpected source-free proof`)
    return {id: `finite_regions_${id}`, countedGoal: goal, certificate}
  })
}
