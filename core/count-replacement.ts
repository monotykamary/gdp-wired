// Optional ordinary count proof for a guarded row replacement. Every supplied
// fact is a count instance or a family-law instance, never a trusted premise.
import {type C, type E, type Law, n, x, get, same, walkOnce} from './machine.ts'
import {type GuardCountContext} from './count-guard-context.ts'
import {discoverCountThresholdWrite} from './count-write-shape.ts'
import {countFrameConditions, fixedCountFrameCase, ownCountLawInstance} from './count-frames.ts'
import {countGuardTree} from './count-guard-tree.ts'
import {countsForReads} from './count-facts.ts'
import {countPrimitiveUnits} from './count-primitive-budget.ts'
import {type CountRequestBuilder, type CountStrategyProof, type CountStrategyOptions, finishCountStrategy, strategyLeafUntil} from './count-strategy.ts'
import {add, k, scale, sub, solve} from './solver.ts'
import {type CountCert, type CountInst, type FrameCut, type Instances, type MapRead, type Path, type Tree, check, countedObligations, frameOk, framePath, linear, mcGoal, substC} from '../kernel/kernel.ts'
import {clock, pastWall, rowsAt, withDeadline} from '../kernel/prove.ts'
import {growCdcl} from '../kernel/cdcl.ts'
import {countSearchView, proveCountQuery} from './count-query.ts'
import {rebasePath} from './count-recovery/rebase-path.ts'
import {replayLinearSkeleton} from './count-recovery/replay-linear-skeleton.ts'

export function proveCountReplacement(context: GuardCountContext, family: Law[], law: Law, seed: Instances, until: number, requestFor: CountRequestBuilder, observe?: (stage: string, checked: boolean) => void, options: CountStrategyOptions = {}): CountStrategyProof | undefined {
  return withDeadline(until, () => {
    const m = context.machine, shape = context.shape, choice = fixedCountFrameCase(m), index = family.indexOf(law)
    if (!choice || index < 0 || clock() >= until || pastWall()) return
    const write = discoverCountThresholdWrite(context.original, shape, choice)
    if (!write || write.increment !== 0 || !write.committedInput || !write.committedCount) return
    const {voteMap, rowMap, width} = shape, sourceName = write.source, newSet = write.input, setMap = context.inputCounts[newSet], quorumMap = context.inputCounts[write.committedInput]
    const outside = context.restrictions.find(e => e.base === setMap && e.input === write.committedInput)?.negative
    if (!setMap || !quorumMap || !outside) return
    const a = x(law.forall + '#'), b = x(law.keys![0]!), i = x(sourceName)
    const flagSub = {vars: {}, maps: {}, flags: Object.fromEntries(Object.entries(m.step.flags ?? {}).map(([name, c]) => [name, c.op === 'all' ? same(x('?' + name), n(1)) : c]))}
    let active = m.step.flags![write.guard]!
    for (let depth = 0; depth < 8; depth++) active = substC(active, flagSub)
    let unsupported = false
    walkOnce(active, (node: any) => {if (node.op === 'flag' || node.op === 'all') unsupported = true})
    if (unsupported) return
    const sourceTerm = get(shape.memberField, i), otherThreshold = get(shape.thresholdField, b), atoms = (c: C): C[] => c.op === 'and' ? c.xs.flatMap(atoms) : [c]
    const sourceVoteMap = voteMap
    const rowFields = new Set([shape.membershipMap])
    const sourceRow = Object.keys(m.counts!).find(name => {const d = m.counts![name]!; let source = false; const fields = new Set<string>(); walkOnce(d.body, (node: any) => {if (node.op === 'get') fields.add(node.map); if (node.op === 'var' && node.name === sourceName) source = true}); return !d.base && source && fields.size === 1 && fields.has(shape.membershipMap)})
    const difference = (left: boolean) => Object.keys(m.counts!).find(name => {const d = m.counts![name]!; if (d.base || d.body.op !== 'if') return false; const cs = atoms(d.body.c); return cs.some(c => c.op === 'not' && (() => {let found = false; walkOnce(c.x, (node: any) => {if (node.op === 'get' && (left ? node.map === newSet : rowFields.has(node.map))) found = true}); return found})()) && cs.some(c => {let found = false; walkOnce(c, (node: any) => {if (node.op === 'get' && (left ? rowFields.has(node.map) : node.map === newSet)) found = true}); return found})})
    const leftMap = difference(true), rightMap = difference(false), intersection = Object.keys(m.counts!).find(name => {const d = m.counts![name]!; if (d.base || d.body.op !== 'if' || atoms(d.body.c).some(c => c.op === 'not')) return false; const fields = new Set<string>(); walkOnce(d.body, (node: any) => {if (node.op === 'get') fields.add(node.map)}); return fields.has(newSet) && fields.has(shape.membershipMap)})
    if (!sourceRow || !leftMap || !rightMap || !intersection) return
    const scope = JSON.stringify([m, family, seed]); let prefix = 'replace$'
    while (scope.includes('"' + prefix)) prefix = '$' + prefix
    const labels = Array.from({length: 15}, (_, j) => prefix + 'w' + j), instances: Instances = {...ownCountLawInstance(law, seed)}
    instances[law.name] = [...(instances[law.name] ?? []), i, b]
    for (const [name, q] of Object.entries(m.step.flags ?? {})) if (q.op === 'all' && !q.keys?.length) instances['?' + name] = [...(seed['?' + name] ?? []), ...labels.map(x)]
    const step = countedObligations(m, family, {[law.name]: instances}, index).at(-1)
    if (!step) return
    const base = requestFor(step.goal, step.decls), reads: MapRead[] = [...base.reads]
    const key = (map: string, args: E[]): E => {const d = m.counts![map.replace(/#$/, '')]!; return d.base ? {op: 'add', a: {op: 'mul', k: d.base, a: args[0]!}, b: args[1]!} : args[0]!}
    const bind = (map: string, args: E[]) => {const at = key(map, args), old = reads.find(r => r[1] === map && JSON.stringify(r[2]) === JSON.stringify(at)); if (old) return old[0]; const name = prefix + 'r' + reads.length; reads.push([name, map, at]); return name}
    const names = {X: bind(sourceRow, [n(0)]), B: bind(rowMap, [i]), preA: bind(rowMap, [a]), A: bind(rowMap + '#', [a]), S: bind(setMap, [n(0)]), Q: bind(quorumMap, [n(0)]), O: bind(outside, [n(0)]), L: bind(leftMap, [n(0)]), R: bind(rightMap, [n(0)]), I: bind(intersection, [n(0)]), V: bind(voteMap + '#', [a, b]), preV: bind(voteMap, [a, b]), weakV: bind(sourceVoteMap, [i, b])}
    const combinations: [number, string][][] = [[[1, names.X], [-1, names.B]], [[1, names.B], [-1, names.X]], [[1, names.A], [-1, names.S]], [[1, names.S], [-1, names.A]], [[1, names.B], [-1, names.L], [-1, names.I]], [[-1, names.B], [1, names.L], [1, names.I]], [[1, names.S], [-1, names.R], [-1, names.I]], [[-1, names.S], [1, names.R], [1, names.I]], [[1, names.Q], [-1, names.B]], [[1, names.O], [-1, names.S]], [[1, names.Q], [1, names.O], [-1, names.L], [-1, names.R], [-1, names.I]], [[1, names.V], [-1, names.O]], [[1, names.Q], [-1, names.weakV]], [[1, names.V], [-1, names.preV]], [[1, names.preA], [-1, names.A]]]
    const counts = countsForReads(step.decls, reads)
    if (!counts?.length) return
    const insts: CountInst[] = combinations.map((terms, j) => ({wit: labels[j]!, below: counts[0]!.below, terms, unit: 0})), cert: CountCert = {reads, insts, picks: [], tree: {leaf: []}, frames: []}, goal = mcGoal(step.goal.hyps, step.decls, cert)
    if (!goal) return
    const ask = (path: Path, stage: string, selected?: number): Tree | undefined => {
      if (clock() >= until || pastWall()) return
      const p = framePath(cert.frames ?? [], [], path)
      if (options.minimalView && selected !== undefined) {
        const minimal = countSearchView(step.goal, step.decls, cert, insts[selected])
        if (minimal) {
          const tree = proveCountQuery(goal, p, until, {query: stage + ':' + selected, minimal, direct: true, minimalUnits: countPrimitiveUnits(900, options.leafUnits), fullUnits: countPrimitiveUnits(900, options.leafUnits), leafUnits: options.leafUnits, trace: options.trace})
          observe?.(stage, !!tree); return tree
        }
      }
      const direct = solve(rowsAt(goal, p), 2000)
      if (direct.kind === 'refuted') {const tree: Tree = {leaf: direct.steps}; if (check(goal, tree, p)) return tree}
      const hyps = selected === undefined ? step.goal.hyps : step.goal.hyps.filter(h => {let unrelated = false; walkOnce(h, (node: any) => {if (node.op === 'if' || node.op === 'var' && node.name.startsWith(prefix + 'w') && node.name !== insts[selected]!.wit) unrelated = true}); return !unrelated})
      const view = selected === undefined ? goal : mcGoal(hyps, step.decls, {reads, insts: [insts[selected]!], picks: []})
      if (!view) return
      const result = growCdcl(view, p, {nodes: 0, until: Math.min(strategyLeafUntil(until, options), clock() + countPrimitiveUnits(900, options.leafUnits))}), tree = 'tree' in result ? rebasePath(view, result.tree, p, p, Math.min(strategyLeafUntil(until, options), clock() + countPrimitiveUnits(600, options.leafUnits)), goal) ?? replayLinearSkeleton(goal, result.tree, p, Math.min(strategyLeafUntil(until, options), clock() + countPrimitiveUnits(600, options.leafUnits))) : undefined
      const checked = !!tree && check(goal, tree, p); observe?.(stage, checked)
      return checked ? tree : undefined
    }
    const split = countGuardTree(until), fact = (j: number, p: Path, yes: (p: Path) => Tree | undefined) => split.rows([add(...combinations[j]!.map(([c, v]) => ({[v]: c})))], p, yes, q => ask(q, 'count-fact', j))
    const facts = (js: number[], p: Path, yes: (p: Path) => Tree | undefined): Tree | undefined => js.length ? fact(js[0]!, p, q => facts(js.slice(1), q, yes)) : yes(p)
    const frame = (p: Path) => {for (const map of [rowMap, voteMap]) {const r = reads.find(r => r[1] === map + '#')!, pre = reads.find(t => t[1] === map && JSON.stringify(t[2]) === JSON.stringify(r[2])); if (!pre) continue; const cut: FrameCut = {post: r[0], pre: pre[0], when: [...p.values()].map(t => t.holds ? t.lin : add(scale(t.lin, -1), k(1)))}; if (frameOk(counts, cut)) cert.frames!.push(cut)}; return ask(p, 'no-op')}
    const arithmetic = (p: Path) => split.rows([{[names.O]: 2, [names.S]: -1}], p, q => ask(q, 'main'), q => {
      const differences: E[] = []; walkOnce(m.step.flags![write.guard], (node: any) => {if (node.op === 'sub') differences.push(node)})
      const cuts = differences.flatMap(e => {if (e.op !== 'sub') return []; const a = linear(e.a, p), b = linear(e.b, p); return a && b ? [sub(b, a)] : []})
      const choose = (j: number, path: Path): Tree | undefined => j === cuts.length ? ask(path, 'overlap') : split.rows([cuts[j]!], path, q => choose(j + 1, q), q => choose(j + 1, q))
      return choose(0, q)
    })
    const domain: C = {op: 'and', xs: [a, b, i].flatMap(t => [{op: '<', a: t, b: counts[0]!.below}, {op: '<', a: t, b: n(width)}])}
    const tree = split.rows(countFrameConditions(choice), new Map(), p => split.condition(domain, p, q => split.condition(active, q, r => split.condition(same(a, i), r, s => facts(Array.from({length: 11}, (_, j) => j), s, t => split.condition({op: '<=', a: otherThreshold, b: sourceTerm}, t, u => fact(11, u, arithmetic), u => fact(12, u, v => ask(v, 'high-threshold')))), s => fact(13, s, t => fact(14, t, u => ask(u, 'unchanged-row')))), frame), q => ask(q, 'outside-domain')), p => ask(p, 'outside-operation'))
    return tree ? finishCountStrategy(m, family, law, instances, voteMap, {...cert, tree}, until, requestFor, undefined, options) : undefined
  })
}
