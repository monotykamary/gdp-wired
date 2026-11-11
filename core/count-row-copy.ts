// Optional structural row-copy proof. Selection and slicing are untrusted;
// every leaf is transported back and checked on the complete count goal.
import {type C, type E, type Law, type Machine, x, n, same, atMost, walkOnce} from './machine.ts'
import {countsForReads} from './count-facts.ts'
import {countPrimitiveUnits} from './count-primitive-budget.ts'
import {countFrameConditions, fixedCountFrameCase, ownCountLawInstance} from './count-frames.ts'
import {discoverCountGuardShape} from './count-guard-shape.ts'
import {discoverCountRowCopy} from './count-copy-shape.ts'
import {countGuardTree} from './count-guard-tree.ts'
import {type CountRequestBuilder, type CountStrategyProof, type CountStrategyOptions, finishCountStrategy, strategyLeafUntil} from './count-strategy.ts'
import {add, k, scale, solve} from './solver.ts'
import {type CountInst, type FrameCut, type Instances, type Path, type Tree, countedObligations, frameOk, framePath, mcGoal} from '../kernel/kernel.ts'
import {growCdcl} from '../kernel/cdcl.ts'
import {clock, pastWall, rowsAt, withDeadline} from '../kernel/prove.ts'
import {rebasePath} from './count-recovery/rebase-path.ts'

export function proveCountRowCopy(m: Machine, family: Law[], law: Law, seed: Instances, until: number, requestFor: CountRequestBuilder, options: CountStrategyOptions = {}): CountStrategyProof | undefined {
  return withDeadline(until, () => {
    if (clock() >= until || pastWall() || !family.includes(law)) return
    const shape = discoverCountGuardShape(m, law, family), choice = fixedCountFrameCase(m)
    if (!shape || !choice) return
    const copy = discoverCountRowCopy(m, shape, choice)
    if (!copy) return
    const from = x(copy.from), to = x(copy.to), a = x(law.forall + '#'), b = x(law.keys![0]!)
    const pairs: [E, E][] = [[a, b], [a, from], [from, b], [from, from]], instances = {...ownCountLawInstance(law, seed)}
    const old = instances[law.name] ?? [], unique = new Map<string, E[]>()
    for (let i = 0; i < old.length; i += 2) unique.set(JSON.stringify(old.slice(i, i + 2)), old.slice(i, i + 2))
    for (const pair of pairs) unique.set(JSON.stringify(pair), pair)
    instances[law.name] = [...unique.values()].flat()
    const step = countedObligations(m, family, {[law.name]: instances}, family.indexOf(law)).at(-1)
    if (!step) return
    const base = requestFor(step.goal, step.decls), reads = base.reads, counts = countsForReads(step.decls, reads)
    if (!counts) return
    const {voteMap, rowMap, width} = shape, key = (p: E, q?: E): E => q ? {op: 'add', a: {op: 'mul', k: width, a: p}, b: q} : p
    const read = (map: string, key: E) => reads.find(r => r[1] === map && JSON.stringify(r[2]) === JSON.stringify(key))?.[0]
    const postVote = read(voteMap + '#', key(a, b)), postRow = read(rowMap + '#', a), bound = counts.find(c => c.v === postVote)?.below
    const voteReads = pairs.map(([p, q]) => read(voteMap, key(p, q))), rowReads = [a, from].map(p => read(rowMap, p))
    if (!postVote || !postRow || !bound || voteReads.some(r => !r) || rowReads.some(r => !r)) return
    const scope = JSON.stringify([m, family, seed, reads]), names: string[] = []
    for (let i = 0; names.length < 6; i++) {const name = `rowCopy$${i}`; if (!scope.includes(JSON.stringify(name))) names.push(name)}
    const voters: CountInst[] = voteReads.map((r, i) => ({wit: names[i]!, below: bound, terms: [[1, postVote], [-1, r!]], unit: 0}))
    const rows: CountInst[] = rowReads.map((r, i) => ({wit: names[4 + i]!, below: bound, terms: [[1, r!], [-1, postRow]], unit: 0}))
    const request = {reads, insts: [...voters, ...rows], picks: []}, goal = mcGoal(step.goal.hyps, step.decls, request)
    if (!goal) return
    const frames: FrameCut[] = [], active = m.step.flags?.[copy.guard]
    if (!active || active.op === 'all') return
    const ask = (path: Path, index: number, frame = false): Tree | undefined => {
      if (clock() >= until || pastWall()) return
      if (frame) for (const map of [voteMap, rowMap]) {
        const post = read(map + '#', map === rowMap ? a : key(a, b)), pre = read(map, map === rowMap ? a : key(a, b))
        if (!post || !pre) return
        const cut: FrameCut = {post, pre, when: [...path.values()].map(t => t.holds ? t.lin : add(scale(t.lin, -1), k(1)))}
        if (frameOk(counts, cut)) frames.push(cut)
      }
      const p = framePath(frames, [], path), selected = reads.find(r => r[0] === voters[index]!.terms[1]![1])!
      const hyps = step.goal.hyps.filter(h => {let unrelated = false; walkOnce(h, (z: any) => {if (z.op === 'get' && z.map === voteMap && JSON.stringify(z.key) !== JSON.stringify(selected[2])) unrelated = true}); return !unrelated})
      const view = mcGoal(hyps, step.decls, {...request, insts: [voters[index]!, rows[index >= 2 ? 1 : 0]!]})
      if (!view) return
      const direct = solve(rowsAt(goal, p), 1000)
      // Intermediate trees are proposals. finishCountStrategy checks the whole
      // original-goal certificate once; do not repeat that work at every leaf.
      if (direct.kind === 'refuted') return {leaf: direct.steps}
      const result = growCdcl(view, p, {nodes: 0, until: Math.min(strategyLeafUntil(until, options), clock() + countPrimitiveUnits(1000, options.leafUnits))})
      const lifted = 'tree' in result ? rebasePath(view, result.tree, p, p, Math.min(strategyLeafUntil(until, options), clock() + countPrimitiveUnits(500, options.leafUnits)), goal) : undefined
      return lifted
    }
    const split = countGuardTree(until)
    const domain: C = {op: 'and', xs: [a, b, from, to].flatMap(t => [{op: '<' as const, a: t, b: bound}, {op: '<' as const, a: t, b: n(width)}])}
    const regions = (p: Path): Tree | undefined => split.condition(same(a, to), p, q => split.condition(same(b, to), q, r => ask(r, 3), r => ask(r, 2)), q => split.condition(same(b, to), q, r => ask(r, 1), r => ask(r, 0)))
    const copies = (p: Path) => split.condition(atMost(to, from), p, regions, regions)
    const tree = split.rows(countFrameConditions(choice), new Map(), p => split.condition(domain, p, q => split.condition(active, q, copies, q => ask(q, 0, true)), q => ask(q, 0)), p => ask(p, 0))
    return tree ? finishCountStrategy(m, family, law, instances, voteMap, {...request, frames, tree}, until, requestFor, undefined, options) : undefined
  })
}
