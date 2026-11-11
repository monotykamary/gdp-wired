// Optional structural quorum/leader strategy. Every auxiliary is regenerated
// and checked on this machine; no saved fact or domain assertion is trusted.
import {type C, type E, type Law, type Machine, n, x, get, same, walkOnce} from './machine.ts'
import {type GuardCountContext} from './count-guard-context.ts'
import {discoverCountThresholdWrite} from './count-write-shape.ts'
import {countFrameConditions, fixedCountFrameCase, ownCountLawInstance} from './count-frames.ts'
import {type CountRequestBuilder, type CountStrategyProof, type CountStrategyOptions, finishCountStrategy, strategyLeafUntil} from './count-strategy.ts'
import {proveLeaderCountFacts} from './count-leader-facts.ts'
import {countPrimitiveUnits} from './count-primitive-budget.ts'
import {guardLinearFact} from './count-guard-facts.ts'
import {boundedQuotient} from './count-bounded-quotient.ts'
import {countGuardTree} from './count-guard-tree.ts'
import {countsForReads} from './count-facts.ts'
import {add, k, scale, sub, solve} from './solver.ts'
import {type CountCert, type CountInst, type FrameCut, type Instances, type LinCut, type MapRead, type Path, type Tree, assumed, canon, check, countedObligations, frameOk, framePath, linear, linOk, mcGoal} from '../kernel/kernel.ts'
import {clock, fullRate, fullWork, grow, pastWall, rowsAt, withDeadline} from '../kernel/prove.ts'
import {growCdcl} from '../kernel/cdcl.ts'
import {countQueryConjuncts, countSearchView, proveCountQuery} from './count-query.ts'
import {rebasePath} from './count-recovery/rebase-path.ts'
import {reframeCountTree} from './count-recovery/reframe-tree.ts'
import {replayLinearSkeleton} from './count-recovery/replay-linear-skeleton.ts'

// The exact structural citation selected by the leader emitter, also exposed to
// prerequisite scheduling. Discovery does not prove the cited law.
export function countLeaderPremise(m:Machine,shape:GuardCountContext['shape'],family:readonly Law[]){
 const mapReads=(t:C|E)=>{const names:string[]=[];walkOnce(t,(node:any)=>{if(node.op==='get'&&m.counts?.[node.map]&&!names.includes(node.map))names.push(node.map)});return names}
 const pairMapsFor=(law:Law)=>mapReads(law.holds).filter(name=>!!m.counts![name]!.base)
 const pairLaws=family.filter(law=>law.forall&&law.keys?.length===3&&pairMapsFor(law).length===2&&pairMapsFor(law).every(name=>{const fields=new Set<string>();walkOnce(m.counts![name]!.body,(node:any)=>{if(node.op==='get')fields.add(node.map)});return fields.size===1&&fields.has(shape.membershipMap)}))
 const eligibilityFor=(law:Law)=>mapReads(law.holds).find(name=>{const d=m.counts![name]!,fields=new Set<string>();walkOnce(d.body,(node:any)=>{if(node.op==='get')fields.add(node.map)});return !d.base&&name!==shape.rowMap&&fields.has(shape.membershipMap)&&!fields.has(shape.memberField)})
 const law=pairLaws.find(law=>eligibilityFor(law))??pairLaws[0]
 return law?{law,maps:pairMapsFor(law),eligibilityMap:eligibilityFor(law)}:undefined
}

export function proveCountLeader(context: GuardCountContext, family: Law[], law: Law, seed: Instances, until: number, requestFor: CountRequestBuilder, observe?: (stage: string, checked: boolean) => void, options: CountStrategyOptions = {}): CountStrategyProof | undefined {
  return withDeadline(until, () => {
    const leaderStart = fullWork()
    const m: Machine = context.machine, shape = context.shape, choice = fixedCountFrameCase(m), index = family.indexOf(law)
    if (!choice || index < 0 || clock() >= until || pastWall()) return
    const write = discoverCountThresholdWrite(context.original, shape, choice)
    if (!write || write.increment !== 1) return
    const saved = proveLeaderCountFacts(context, family, law, until, requestFor, options.leafUnits)
    if (!saved) return
    const upperFact = saved.facts.find(f => f.proposal.kind === 'guard-complement-upper')
    if (!upperFact || upperFact.proposal.when.length < 4) return
    const {rowMap, voteMap} = shape, guardMap = write.input, i = x(write.source), a = x(law.forall + '#'), b = x(law.keys![0]!)
    const selectedPair = countLeaderPremise(m, shape, family), pairLaw = selectedPair?.law, eligibilityMap = selectedPair?.eligibilityMap
    options.trace?.({query: 'leader-pair-premise', outcome: pairLaw ? 'selected' : 'missing', premises: pairLaw ? [pairLaw.name] : [], eligibilityMap})
    if (!pairLaw || !selectedPair) return
    const pairMaps = selectedPair.maps, onlyMap = pairMaps.find(name => {let neg = false; walkOnce(m.counts![name]!.body, (node: any) => {if (node.op === 'not') neg = true}); return neg}), bothMap = pairMaps.find(name => name !== onlyMap)
    if (!onlyMap || !bothMap) return
    const key = (map: string, args: E[]): E => {const d = m.counts![map.replace(/#$/, '')]!; return d.base ? {op: 'add', a: {op: 'mul', k: d.base, a: args[0]!}, b: args[1]!} : args[0]!}
    const read = (map: string, args: E[]) => get(map, key(map, args)), sum = (a: E, b: E): E => ({op: 'add', a, b})
    const na = sum(read(onlyMap, [a, i]), read(bothMap, [a, i])), ni = sum(read(onlyMap, [i, a]), read(bothMap, [a, i]))
    let upper = 0; walkOnce(m.pre ?? [], (node: any) => {if (node.op === '<=' && node.b.op === 'const') upper = Math.max(upper, node.b.value)})
    if (!Number.isSafeInteger(upper) || upper < 1 || upper > 4096) return
    const sourceVoteMap = voteMap, sMap = context.inputCounts[guardMap], outsideMap = context.restrictions.find(e => e.base === rowMap && e.input === guardMap)?.negative
    const inputRowMap = Object.keys(m.counts!).find(name => {const d = m.counts![name]!; let source = false; const fields = new Set<string>(); walkOnce(d.body, (node: any) => {if (node.op === 'get') fields.add(node.map); if (node.op === 'var' && node.name === write.source) source = true}); return !d.base && source && fields.size === 1 && fields.has(shape.membershipMap)})
    if (!sMap || !outsideMap || !inputRowMap) return
    const scope = JSON.stringify([m, family, seed]); let prefix = 'ordinary$'
    while (scope.includes('"' + prefix)) prefix = '$' + prefix
    const labels = ['subset', 'union', 'bound-a', 'bound-i', 'row-source', 'source-row', 'term', ...(eligibilityMap ? ['eligible-source', 'eligible-target'] : [])].map(name => prefix + name)
    const halves = [boundedQuotient(na, 2, upper), boundedQuotient(ni, 2, upper)]
    const pairTerms = [a, i, ...halves], pairInstance = assumed([pairLaw], {[pairLaw.name]: pairTerms})[0]!
    const instances: Instances = {...ownCountLawInstance(law, seed), [pairLaw.name]: [...(seed[pairLaw.name] ?? []), ...pairTerms]}
    // The source row uses this same restricted invariant, not a weaker law
    // that may already have been refuted by candidate admission.
    instances[law.name] = [...(instances[law.name] ?? []), i, b]
    for (const [name, q] of Object.entries(m.step.flags ?? {})) if (q.op === 'all' && !q.keys?.length) {let relevant = false; walkOnce(q.c, (node: any) => {if (node.op === 'get' && node.map === guardMap) relevant = true}); if (relevant) instances['?' + name] = [...(seed['?' + name] ?? []), ...labels.map(x)]}
    const step = countedObligations(m, family, {[law.name]: instances}, index).at(-1)!
    const base = requestFor(step.goal, step.decls), reads: MapRead[] = [...base.reads]
    const bind = (map: string, args: E[]) => {const term = key(map, args), old = reads.find(r => r[1] === map && JSON.stringify(r[2]) === JSON.stringify(term)); if (old) return old[0]; const name = prefix + 'read' + reads.length; reads.push([name, map, term]); return name}
    const names = {S: bind(sMap, [n(0)]), X: bind(inputRowMap, [n(0)]), A: bind(rowMap, [a]), B: bind(rowMap, [i]), O: bind(outsideMap, [a]), L: bind(onlyMap, [a, i]), R: bind(onlyMap, [i, a]), I: bind(bothMap, [a, i]), V: bind(sourceVoteMap, [i, b])}
    const eligible = eligibilityMap ? {source: bind(eligibilityMap, [i]), target: bind(eligibilityMap, [a]), postVotes: bind(voteMap + '#', [a, b])} : undefined
    for (const f of saved.facts) for (const [, name] of [...f.cut.pos, ...f.cut.neg]) {const r = saved.reads.find(r => r[0] === name)!; if (!reads.some(t => t[1] === r[1] && JSON.stringify(t[2]) === JSON.stringify(r[2]))) reads.push([prefix + 'read' + reads.length, r[1], r[2]])}
    const counts = countsForReads(step.decls, reads)
    if (!counts?.length) return
    const bound = counts[0]!.below, insts: CountInst[] = [
      {wit: labels[0]!, below: bound, terms: [[1, names.S], [-1, names.B]], unit: 0},
      {wit: labels[1]!, below: bound, terms: [[1, names.S], [1, names.O], [-1, names.A], [-1, names.R]], unit: 0},
      {wit: labels[2]!, below: bound, terms: [[1, names.A]], unit: -1},
      {wit: labels[3]!, below: bound, terms: [[1, names.B]], unit: -1},
      {wit: labels[4]!, below: bound, terms: [[1, names.X], [-1, names.B]], unit: 0},
      {wit: labels[5]!, below: bound, terms: [[1, names.B], [-1, names.X]], unit: 0},
      {wit: labels[6]!, below: bound, terms: [[1, names.S], [-1, names.V]], unit: 0},
      ...(eligible ? [
        {wit: labels[7]!, below: bound, terms: [[1, names.S], [-1, eligible.source]], unit: 0},
        {wit: labels[8]!, below: bound, terms: [[1, eligible.postVotes], [-1, eligible.target]], unit: 0}
      ] as CountInst[] : [])
    ]
    const cert: CountCert = {reads, insts, picks: [], tree: {leaf: []}, lins: [], frames: []}, goal = mcGoal(step.goal.hyps, step.decls, cert)
    if (!goal) return
    const remap = (side: [number, string][]) => side.map(([coefficient, name]): [number, string] => {const r = saved.reads.find(r => r[0] === name)!; return [coefficient, reads.find(t => t[1] === r[1] && JSON.stringify(t[2]) === JSON.stringify(r[2]))![0]]})
    for (const fact of saved.facts) {const cut: LinCut = {...fact.cut, pos: remap(fact.cut.pos), neg: remap(fact.cut.neg)}; if (!linOk(counts, cut)) return; cert.lins!.push(cut)}
    options.trace?.({query: 'leader-setup', units: (fullWork() - leaderStart) / fullRate})
    const partition = (terms: [number, string][], name: string): boolean => {
      const started = fullWork(), leafEnd = strategyLeafUntil(until, options)
      let searchEnd: number | undefined
      const fact = guardLinearFact(step.decls, reads, {name, kind: 'partition', when: [], terms}, Math.min(leafEnd, clock() + countPrimitiveUnits(600, options.leafUnits)), event => {searchEnd = event.searchEnd})
      const capped = leafEnd < until && (searchEnd ?? clock()) >= leafEnd
      if (fact && !capped) cert.lins!.push(fact.cut)
      options.trace?.({query: 'partition', name, outcome: capped ? 'leaf-cap' : fact ? 'proposed' : 'declined', units: (fullWork() - started) / fullRate})
      return !!fact && !capped
    }
    for (const [terms, name] of [
      [[[1, names.A], [-1, names.L], [-1, names.I]], 'first row partition <='],
      [[[-1, names.A], [1, names.L], [1, names.I]], 'first row partition >='],
      [[[1, names.B], [-1, names.R], [-1, names.I]], 'source row partition <='],
      [[[-1, names.B], [1, names.R], [1, names.I]], 'source row partition >='],
      [[[1, names.O], [-1, names.A]], 'guard complement subset']
    ] as [[number, string][], string][]) if (!partition(terms, name)) return
    const split = countGuardTree(until)
    const askInner = (path: Path, stage: string): Tree | undefined => {
      if (clock() >= until || pastWall()) return
      const p = framePath(cert.frames ?? [], [], path, [], cert.lins), queryEnd = strategyLeafUntil(until, options)
      if (options.minimalView && stage === 'count-fact') {
        const selected = insts.find(inst => {const row = add(...inst.terms.map(([c, v]) => ({[v]: c})), scale(linear(inst.below, p)!, inst.unit)); return p.get(canon(row))?.holds === false})
        const minimal = selected && countSearchView(step.goal, step.decls, cert, selected)
        if (minimal) {
          const tree = proveCountQuery(goal, p, until, {query: stage, minimal, direct: true, minimalUnits: countPrimitiveUnits(600, options.leafUnits), fullUnits: countPrimitiveUnits(250, options.leafUnits), leafUnits: Math.max(0, queryEnd - clock()), trace: options.trace})
          observe?.(stage, !!tree); return tree
        }
      }
      if (stage === 'quorum-transport') {
        const started = fullWork(), end = until
        const required = new Set([names.S, names.O, names.A, names.B, names.L, names.R, names.I, ...(eligible ? [eligible.source, eligible.target] : [])])
        const domains = step.goal.hyps.flatMap(h => countQueryConjuncts(h)).filter(h => h.op === '<' && JSON.stringify(h.b) === JSON.stringify(bound) && [a, i].some(key => JSON.stringify(key) === JSON.stringify(h.a)))
        const minimal = mcGoal([...countQueryConjuncts(m.pre ?? {op: 'and', xs: []}), ...domains, pairInstance], step.decls, {reads: reads.filter(([id]) => required.has(id)), insts: [], picks: []})
        const clipped: E[] = []
        walkOnce(pairInstance, (node: any) => {if (node.op === 'sub' && !clipped.some(e => JSON.stringify(e) === JSON.stringify(node))) clipped.push(node)})
        if (!minimal || clipped.length !== 2) return
        // Match natural subtraction's own decision: right <= left.
        const cuts = [sub({[names.O]: 1}, linear(halves[0]!, p)!), sub({[names.S]: 1}, linear(halves[1]!, p)!), ...clipped.map(e => e.op === 'sub' ? sub(linear(e.b, p)!, linear(e.a, p)!) : {})]
        const local = countGuardTree(end)
        const close = (at: Path): Tree | undefined => {
          const before = fullWork(), leafEnd = strategyLeafUntil(until, options)
          if (clock() >= leafEnd) return
          const rows = rowsAt(minimal, at), result = withDeadline(leafEnd, () => solve(rows, 2000, true, () => clock() < leafEnd && !pastWall())), capped = leafEnd < until && clock() >= leafEnd
          const tree: Tree | undefined = result.kind === 'refuted' ? {leaf: result.steps} : undefined
          const accepted = !capped && tree && check(minimal, tree, at) ? tree : undefined
          options.trace?.({query: 'quorum-linear-leaf', outcome: accepted ? 'proposed' : capped ? 'leaf-cap' : result.kind, units: (fullWork() - before) / fullRate, hyps: minimal.hyps.length, rows: rows.length, ...(!accepted ? {goal: minimal, path: [...at.values()], result} : {})})
          return accepted
        }
        const choose = (j: number, at: Path): Tree | undefined => j === cuts.length ? close(at) : local.rows([cuts[j]!], at, j < 2 ? close : q => choose(j + 1, q), q => choose(j + 1, q))
        if (pairInstance.op !== 'or' || pairInstance.xs[0]?.op !== 'not') return
        const guard = pairInstance.xs[0].x, disabled = pairInstance.xs.slice(2), base = m.counts![onlyMap]!.base!
        const enter = (j: number, at: Path): Tree | undefined => j < disabled.length
          ? local.condition(disabled[j]!, at, close, next => enter(j + 1, next))
          : local.condition({op: '<', a, b: n(base)}, at, next => local.condition({op: '<', a: i, b: n(base)}, next, ready => choose(0, ready), close), close)
        // Make the law's raw atoms explicit too: aliases imply them linearly,
        // but truth() does not infer an equivalent decision through a binding.
        const tree = local.condition(guard, p, at => enter(0, at), close), lifted = tree && rebasePath(minimal, tree, p, p, end, goal), checked = lifted && check(goal, lifted, p)
        options.trace?.({query: stage, mode: 'linear', outcome: checked ? 'proposed' : tree ? 'transport-rejected' : 'declined', units: (fullWork() - started) / fullRate, hyps: minimal.hyps.length, fullHyps: goal.hyps.length})
        observe?.(stage, !!checked)
        return checked ? lifted : undefined
      }
      if (stage === 'count-fact') {
        const selected = insts.find(inst => {const row = add(...inst.terms.map(([c, v]) => ({[v]: c})), scale(linear(inst.below, p)!, inst.unit)); return p.get(canon(row))?.holds === false})
        if (selected) {
          const hyps = step.goal.hyps.filter(h => {let choice = false; walkOnce(h, (node: any) => {if (node.op === 'if') choice = true}); return !choice})
          const view = mcGoal(hyps, step.decls, {reads, insts: [selected], picks: []})!
          const result = growCdcl(view, p, {nodes: 0, until: Math.min(queryEnd, clock() + countPrimitiveUnits(600, options.leafUnits))}), tree = 'tree' in result && clock() < queryEnd ? rebasePath(view, result.tree, p, p, until, goal) ?? replayLinearSkeleton(goal, result.tree, p, until) : undefined
          if (tree && check(goal, tree, p)) return tree
        }
      }
      if (stage === 'bounded-floor') for (const value of [na, ni]) {
        const half = boundedQuotient(value, 2, upper), twice: E = {op: 'mul', k: 2, a: half}
        for (const fact of [{op: '<=', a: twice, b: value}, {op: '<=', a: value, b: sum(twice, n(1))}] as C[]) {
          if (fact.op !== '<=') continue
          const row = sub(linear(fact.a, p)!, linear(fact.b, p)!)
          if (p.get(canon(row))?.holds !== false) continue
          const auxiliary = {name: 'ordinary bounded floor', hyps: [{op: '<=' as const, a: value, b: n(upper)}, {op: 'not' as const, x: fact}]}
          const result = grow(auxiliary, new Map(), {nodes: 0, until: Math.min(queryEnd, clock() + countPrimitiveUnits(600, options.leafUnits))}), tree = 'tree' in result && clock() < queryEnd && check(auxiliary, result.tree) ? rebasePath(auxiliary, result.tree, new Map(), p, until, goal) ?? replayLinearSkeleton(goal, result.tree, p, until) : undefined
          if (tree && check(goal, tree, p)) return tree
        }
      }
      if (stage === 'row-sum-bound') {
        const domains = step.goal.hyps.flatMap(h => countQueryConjuncts(h)).filter(h => h.op === '<' && JSON.stringify(h.b) === JSON.stringify(bound) && [a, i].some(key => JSON.stringify(key) === JSON.stringify(h.a)))
        const minimal = mcGoal([...countQueryConjuncts(m.pre ?? {op: 'and', xs: []}), ...domains], step.decls, {reads, insts: [], picks: []})
        if (minimal) return proveCountQuery(goal, p, until, {query: stage, minimal, direct: true, leafUnits: Math.max(0, queryEnd - clock()), trace: options.trace})
      }
      // Stage-specific auxiliary views above have the first chance. The full
      // goal's direct solve is the last inexpensive fallback, not the first.
      if (clock() >= queryEnd) {options.trace?.({query: stage, outcome: 'leaf-cap', units: 0}); return}
      const direct = solve(rowsAt(goal, p), 2000, true, () => clock() < queryEnd && !pastWall())
      if (clock() >= queryEnd) {options.trace?.({query: stage, outcome: 'leaf-cap', units: 0}); return}
      if (direct.kind === 'refuted') {const tree: Tree = {leaf: direct.steps}; if (check(goal, tree, p)) return tree}
      const queryStart = fullWork()
      const result = growCdcl(goal, p, {nodes: 0, until: Math.min(queryEnd, clock() + countPrimitiveUnits(250, options.leafUnits))}), capped = queryEnd < until && clock() >= queryEnd, checked = !capped && 'tree' in result && check(goal, result.tree, p)
      observe?.(stage, checked)
      options.trace?.({query: stage, outcome: capped ? 'leaf-cap' : checked ? 'proposed' : 'stuck' in result ? result.stuck : 'rejected', units: (fullWork() - queryStart) / fullRate, ...(!checked ? {goal, path: [...p.values()], ...('witness' in result ? {witness: result.witness} : {}), ...('why' in result ? {why: result.why} : {})} : {})})
      return checked && 'tree' in result ? result.tree : undefined
    }
    const memo = new Map<string, {path: Path, tree: Tree}[]>()
    const ask = (path: Path, stage: string): Tree | undefined => {
      const started = fullWork(), p = framePath(cert.frames ?? [], [], path, [], cert.lins)
      const minimal = countSearchView(step.goal, step.decls, cert) ?? goal
      const key = stage + '\n' + JSON.stringify(rowsAt(minimal, p).filter(row => row.src && 'fact' in row.src).map(row => canon(row.lin)).sort())
      for (const entry of memo.get(key) ?? []) {
        const tree = rebasePath(goal, entry.tree, entry.path, p, until, goal)
        if (tree && check(goal, tree, p)) {
          const framed = reframeCountTree(goal, tree, p, path, at => framePath(cert.frames ?? [], [], at, [], cert.lins), until)
          if (framed) {
            options.trace?.({query: 'leader-ask', stage, kind: 'ask-total', mode: 'memo', outcome: 'proposed', units: (fullWork() - started) / fullRate, remaining: until - clock()})
            return framed
          }
        }
      }
      const tree = askInner(path, stage)
      if (tree && check(goal, tree, p)) {
        const entries = memo.get(key) ?? []
        if (entries.length < 8) {entries.push({path: new Map(p), tree}); memo.set(key, entries)}
      }
      const framed = tree && reframeCountTree(goal, tree, p, path, at => framePath(cert.frames ?? [], [], at, [], cert.lins), until)
      options.trace?.({query: 'leader-ask', stage, kind: 'ask-total', mode: 'search', outcome: framed ? 'proposed' : clock() >= until ? 'pool-exhausted' : 'declined', units: (fullWork() - started) / fullRate, remaining: until - clock()})
      return framed
    }
    const frame = (p: Path) => {for (const r of reads.filter(r => r[1] === voteMap + '#')) {const pre = reads.find(t => t[1] === voteMap && JSON.stringify(t[2]) === JSON.stringify(r[2])); if (!pre) continue; const cut: FrameCut = {post: r[0], pre: pre[0], when: [...p.values()].map(t => t.holds ? t.lin : add(scale(t.lin, -1), k(1)))}; if (frameOk(counts, cut)) cert.frames!.push(cut)}; return ask(p, 'no-op')}
    const active = upperFact.proposal.when[1]!, postBound = upperFact.proposal.when[3]!
    // These facts do not depend on the target-column/source equality. Prove
    // them once before that exhaustive split, rather than once in every arm.
    const factRows = (p: Path) => [add({[names.X]: 1, [names.S]: -2}, k(1)), ...[...insts.slice(0, 6), ...(eligible ? [insts[7]!] : [])].map(inst => add(...inst.terms.map(([c, v]) => ({[v]: c})), scale(linear(inst.below, p)!, inst.unit)))]
    const transportRows = (at: Path) => ({
      floors: [na, ni].flatMap(value => {const half = boundedQuotient(value, 2, upper), twice: E = {op: 'mul', k: 2, a: half}; return [sub(linear(twice, at)!, linear(value, at)!), add(sub(linear(value, at)!, linear(twice, at)!), k(-1))]}),
      domains: [na, ni].map(value => add(linear(value, at)!, k(-upper)))
    })
    const finish = (p: Path): Tree | undefined => {
      return split.condition(postBound, p, r => {
        const transport = (at: Path): Tree | undefined => {
          const {floors, domains} = transportRows(at)
          return split.rows(domains, at, s => split.rows(floors, s, t => split.rows([{[names.O]: 2, [names.A]: -1}], t, u => ask(u, 'main-with-transport'), u => ask(u, 'quorum-transport')), t => ask(t, 'bounded-floor')), s => ask(s, 'row-sum-bound'))
        }
        if (!eligible) return transport(r)
        // A source quorum is eligible by the retained per-member guards. For a
        // different target row, its post-votes are a subset of pre-eligibility.
        // Both are proposed ordinary count witnesses, never assumed aliases.
        return split.condition(same(a, i), r, transport, s => split.rows([{[eligible.postVotes]: 1, [eligible.target]: -1}], s, t => split.rows([{[eligible.target]: 2, [names.A]: -1}], t, u => ask(u, 'disabled-target'), transport), t => ask(t, 'count-fact')))
      }, r => ask(r, 'term-bound'))
    }
    const domain: C = {op: 'and', xs: [a, b, i].flatMap(t => [{op: '<', a: t, b: bound}, {op: '<', a: t, b: n(shape.width)}])}
    const cases = (p: Path) => split.condition(same(b, i), p, finish, finish)
    const beforeCases = (p: Path): Tree | undefined => {
      const {domains, floors} = transportRows(p)
      const queries = [...domains.map(row => ({row, name: 'row-sum-bound', reject: (q: Path) => ask(q, 'row-sum-bound')})), ...floors.map(row => ({row, name: 'bounded-floor', reject: (q: Path) => ask(q, 'bounded-floor')}))]
      const afterCommon = (q: Path) => !eligible ? cases(q) : split.condition(same(a, i), q, cases, r => split.hoist([{row: {[eligible.postVotes]: 1, [eligible.target]: -1}, name: 'eligibility', reject: (s: Path) => ask(s, 'count-fact')}], [same(b, i)], r, cases, options.trace))
      return split.hoist(queries, [same(a, i), same(b, i)], p, afterCommon, options.trace)
    }
    const tree = split.rows(countFrameConditions(choice), new Map(), p => split.condition(domain, p, q => split.condition(active, q, r => split.rows(factRows(r), r, beforeCases, q => ask(q, 'count-fact')), frame), q => ask(q, 'outside-domain')), p => ask(p, 'outside-operation'))
    if (!tree) return
    let last = fullWork()
    const proof = finishCountStrategy(m, family, law, instances, voteMap, {...cert, tree}, until, requestFor, (stage, checked) => {
      const now = fullWork()
      options.trace?.({query: 'leader-final', stage, outcome: checked ? 'checked' : 'rejected', units: (now - last) / fullRate})
      last = now
    }, options)
    options.trace?.({query: 'leader-total', outcome: proof ? options.deferToComposition ? 'proposed' : 'checked' : 'declined', units: (fullWork() - leaderStart) / fullRate})
    return proof
  })
}
