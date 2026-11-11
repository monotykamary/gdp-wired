// Pointwise, ordinary checked alternative to the global row-copy witnesses.
// A failed auxiliary proof declines; neither discovery nor a candidate is trusted.
import {type C, type E, type Law, type Machine, all, n, not, same, x} from './machine.ts'
import {countFrameConditions, fixedCountFrameCase, ownCountLawInstance} from './count-frames.ts'
import {discoverCountGuardShape} from './count-guard-shape.ts'
import {discoverCountRowCopy} from './count-copy-shape.ts'
import {countsForReads} from './count-facts.ts'
import {guardLinearFact, type GuardCountProposal} from './count-guard-facts.ts'
import {countGuardTree} from './count-guard-tree.ts'
import {type CountRequestBuilder, type CountStrategyProof, type CountStrategyOptions, finishCountStrategy} from './count-strategy.ts'
import {add, k, scale, solve} from './solver.ts'
import {type FrameCut, type Instances, type LinCut, type Path, type Tree, countedObligations, frameOk, framePath, mcGoal, truth} from '../kernel/kernel.ts'
import {late, rowsAt, withDeadline} from '../kernel/prove.ts'
export function proveCountRowCopyLinear(m: Machine, family: Law[], law: Law, seed: Instances, until: number, requestFor: CountRequestBuilder, observe?: (stage: string, checked: boolean) => void, options: CountStrategyOptions = {}): CountStrategyProof | undefined {
  return withDeadline(until, () => {
    if (late(until) || !family.includes(law)) return
    const shape = discoverCountGuardShape(m, law, family), choice = fixedCountFrameCase(m)
    if (!shape || !choice) return
    const copy = discoverCountRowCopy(m, shape, choice), active = copy && m.step.flags?.[copy.guard]
    if (!copy || !active || active.op === 'all') return
    const from = x(copy.from), to = x(copy.to), a = x(law.forall + '#'), b = x(law.keys![0]!), pairs: [E, E][] = [[a, b], [a, from], [from, b], [from, from]], instances = {...ownCountLawInstance(law, seed)}
    const unique = new Map<string, E[]>(), old = instances[law.name] ?? []
    for (let i = 0; i < old.length; i += 2) unique.set(JSON.stringify(old.slice(i, i + 2)), old.slice(i, i + 2))
    for (const pair of pairs) unique.set(JSON.stringify(pair), pair)
    instances[law.name] = [...unique.values()].flat()
    const step = countedObligations(m, family, {[law.name]: instances}, family.indexOf(law)).at(-1)
    if (!step) return
    const base = requestFor(step.goal, step.decls), reads = base.reads, counts = countsForReads(step.decls, reads)
    if (!counts) return
    const key = (p: E, q?: E): E => q ? {op: 'add', a: {op: 'mul', k: shape.width, a: p}, b: q} : p
    const read = (map: string, key: E) => reads.find(r => r[1] === map && JSON.stringify(r[2]) === JSON.stringify(key))?.[0]
    const postVote = read(shape.voteMap + '#', key(a, b)), postRow = read(shape.rowMap + '#', a), bound = counts.find(c => c.v === postVote)?.below
    const votes = pairs.map(([p, q]) => read(shape.voteMap, key(p, q))), rows = [a, from].map(p => read(shape.rowMap, p))
    if (!postVote || !postRow || !bound || votes.some(r => !r) || rows.some(r => !r)) return
    const operation = same(x(choice.name), n(choice.value)), domain: C = all(...[a, b, from, to].flatMap(t => [{op: '<' as const, a: t, b: bound}, {op: '<' as const, a: t, b: n(shape.width)}])), regions: C[][] = [[not(same(a, to)), not(same(b, to))], [not(same(a, to)), same(b, to)], [same(a, to), not(same(b, to))], [same(a, to), same(b, to)]]
    const when = [...(m.pre ? [m.pre] : []), operation, domain, active], proposals: GuardCountProposal[] = votes.map((pre, i) => ({name: 'copy voter inclusion ' + i, kind: 'pointwise-copy', when: [...when, ...regions[i]!], terms: [[1, postVote], [-1, pre!]]}))
    rows.forEach((pre, i) => proposals.push({name: 'copy row lower bound ' + i, kind: 'pointwise-copy', when: [...when, i ? same(a, to) : not(same(a, to))], terms: [[1, pre!], [-1, postRow]]}))
    const lins: LinCut[] = []
    for (const proposal of proposals) {if (late(until)) return; const fact = guardLinearFact(step.decls, reads, proposal, until); observe?.(proposal.name, !!fact); if (!fact) return; lins.push(fact.cut)}
    const request = {reads, insts: [], picks: [], lins}, goal = mcGoal(step.goal.hyps, step.decls, request)
    if (!goal) return
    const frames: FrameCut[] = [], ask = (path: Path, frame = false, stage = 'active-region'): Tree | undefined => {
      if (late(until)) return
      if (frame) for (const map of [shape.voteMap, shape.rowMap]) {
        const post = read(map + '#', map === shape.rowMap ? a : key(a, b)), pre = read(map, map === shape.rowMap ? a : key(a, b))
        if (!post || !pre) return
        const cut = {post, pre, when: [...path.values()].map(t => t.holds ? t.lin : add(scale(t.lin, -1), k(1)))}
        if (frameOk(counts, cut)) frames.push(cut)
      }
      const result = solve(rowsAt(goal, framePath(frames, [], path, [], lins)), 2000)
      if (result.kind !== 'refuted') observe?.('close:' + stage + ':' + result.kind + ':' + JSON.stringify({frames: frames.length, activeCuts: lins.map(l => l.when.map(c => truth(c, path))), path: [...path.values()]}), false)
      return result.kind === 'refuted' ? {leaf: result.steps} : undefined
    }
    const split = countGuardTree(until), region = (path: Path) => split.condition(same(a, to), path, p => split.condition(same(b, to), p, q => ask(q), q => ask(q)), p => split.condition(same(b, to), p, q => ask(q), q => ask(q)))
    const body = (path: Path) => split.rows(countFrameConditions(choice), path, p => split.condition(domain, p, q => split.condition(active, q, region, q => ask(q, true, 'inactive')), q => ask(q, false, 'outside-domain')), q => ask(q, false, 'outside-operation'))
    const tree = m.pre ? split.condition(m.pre, new Map(), body, p => ask(p, false, 'outside-precondition')) : body(new Map())
    observe?.('whole-step-tree', !!tree)
    return tree ? finishCountStrategy(m, family, law, instances, shape.voteMap, {...request, frames, tree}, until, requestFor, undefined, options) : undefined
  })
}
