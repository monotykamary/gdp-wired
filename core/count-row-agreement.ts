// Experimental written-row proposer. Standalone results check INIT and STEP;
// composition may request only an unchecked STEP proposal for its final check.
// The optional composition hook owns production dispatch; no trusted shortcut.
import {type C, type E, type Law, type Machine, n, same, walkOnce, x} from './machine.ts'
import {type RowAgreementShape} from './row-agreement-shape.ts'
import {countGuardTree} from './count-guard-tree.ts'
import {countFrameConditions, fixedCountFrameCase} from './count-frames.ts'
import {type CountRequestBuilder, type CountStrategyOptions, type CountStrategyProof, strategyLeafUntil} from './count-strategy.ts'
import {type CountCert, type Goal, type Instances, type Path, type Tree, canon, check, checkMC, countedObligations, leafConstraints, mcGoal, substC, substE, truth} from '../kernel/kernel.ts'
import {clock, fullRate, fullWork, pastWall, withDeadline} from '../kernel/prove.ts'
import {growCdcl} from '../kernel/cdcl.ts'
import {seedCountWitnessFlags} from './count-witness-flags.ts'
import {refuteFast} from './solver.ts'
import {rowSymmetryCache} from './count-row-symmetry.ts'
import {operationRefutation} from './count-row-reindex.ts'
import {countPremiseView} from './count-premise-view.ts'
import {rebasePath} from './count-recovery/rebase-path.ts'

// Operation tests are often already inlined, and a row equality can be an
// ancestor of the operation guard. Prune only branches decided by the fixed
// operation; proposing extra row splits is safe, omitting them loses proofs.
export function rowAgreementWrittenKeys(m: Machine, shape: RowAgreementShape): string[] {
  const choice = fixedCountFrameCase(m)
  if (!choice) return []
  const path: Path = new Map(countFrameConditions(choice).map(lin => [canon(lin), {lin, holds: true}]))
  const rows = new Set<string>(), flags: Record<string, C> = Object.create(null)
  for (const [name, condition] of Object.entries(m.step.flags ?? {})) flags[name] = condition.op === 'all' ? same(x('?' + name), n(1)) : substC(condition, {vars: {}, maps: {}, flags})
  for (const map of [shape.map, ...shape.fields, ...shape.markers.map(marker => marker.map)]) {
    const write = m.step.maps?.[map]
    if (!write) continue
    if (!('each' in write)) {
      if (write.key.op !== 'var' || !m.inputs.includes(write.key.name)) continue
      let guarded = false, active = false
      walkOnce(substE(write.value, {vars: {}, maps: {}, flags}), (part: any) => {
        if (part.op !== '=') return
        const [v, value] = part.a.op === 'var' ? [part.a, part.b] : [part.b, part.a]
        if (v.op !== 'var' || v.name !== choice.name || value.op !== 'const' || !choice.values.includes(value.value)) return
        guarded = true; active ||= value.value === choice.value
      })
      if (!guarded || active) rows.add(write.key.name)
      continue
    }
    const visit = (value: unknown): void => {
      if (!value || typeof value !== 'object') return
      const node = value as Record<string, unknown>
      if (node.op === 'if') {
        const condition = substC(node.c as C, {vars: {}, maps: {}, flags}), active = truth(condition, path)
        if (active !== false) walkOnce(condition, (part: any) => {
          if (part.op !== '=') return
          const [v, key] = part.a.op === 'var' && part.a.name === write.each ? [part.a, part.b] : [part.b, part.a]
          if (v.op === 'var' && v.name === write.each && key.op === 'var' && m.inputs.includes(key.name)) rows.add(key.name)
        })
        if (active !== false) visit(node.then)
        if (active !== true) visit(node.else)
        return
      }
      for (const child of Array.isArray(value) ? value : Object.values(node)) visit(child)
    }
    visit(write.value)
  }
  return [...rows]
}
export type RowAgreementTrace = {stage: 'leaf', outcome: string, goal: Goal, path: Path, hyps?: number, units?: number, witness?: Record<string, number>, method?: 'linear' | 'cdcl' | 'symmetry', symmetryEnabled?: boolean}
export type RowAgreementOptions = CountStrategyOptions & {premiseScoped?: boolean, observe?: (trace: RowAgreementTrace) => void, seedInstances?: Instances, onlySeededPremises?: boolean, witnessFlags?: boolean, fastClosure?: boolean, symmetryReuse?: boolean, diagonalFirst?: boolean, sparseOwn?: boolean, operationPath?: boolean, diagonalAlias?: boolean, framePremisesOnly?: boolean, ownRows?: E[], premiseRows?: E[]}
// An unchecked INIT proposal for a single-check composition. No STEP or supplied premise.
export function proposeRowAgreementInitial(m: Machine, family: Law[], law: Law, until: number, requestFor: CountRequestBuilder): CountCert | undefined {
  return withDeadline(until, () => {
    const target = family.indexOf(law)
    if (target < 0 || clock() >= until || pastWall()) return
    const packets = countedObligations(m, family, {}, target)
    if (packets.length !== 2) return
    const packet = packets[0]!, request = requestFor(packet.goal, packet.decls), goal = mcGoal(packet.goal.hyps, packet.decls, request)
    const result = goal && growCdcl(goal, new Map(), {nodes: 0, until})
    return result && 'tree' in result ? {...request, tree: result.tree} : undefined
  })
}
export function proveRowAgreementCase(m: Machine, family: Law[], law: Law, shape: RowAgreementShape, until: number, requestFor: CountRequestBuilder, options: RowAgreementOptions = {}): CountStrategyProof | undefined {
  return withDeadline(until, () => {
    const index = family.indexOf(law)
    if (index < 0 || clock() >= until || pastWall() || !law.forall || law.keys?.length !== 2) return
    const frameOnly = options.framePremisesOnly && fixedCountFrameCase(m) && !rowAgreementWrittenKeys(m, shape).length
    const a = x(law.forall + '#'), b = x(law.keys[0]!), column = x(law.keys[1]!), keyed = new Set<string>()
    walkOnce(m.step.maps, (node: any) => {if (node.op === 'get' && !m.counts?.[node.map] && node.key.op === 'var' && m.inputs.includes(node.key.name)) keyed.add(node.key.name)})
    // A small proposal pool: the goal's two rows and actual request row keys.
    // No count law is seeded indiscriminately, and no supplied premise is added.
    const rows: E[] = [a, b, ...(options.premiseRows ?? [...keyed].slice(0, 4).map(x))], instances: Instances = Object.fromEntries(Object.entries(options.seedInstances ?? {}).map(([name, terms]) => [name, [...terms]]))
    const ownRows = options.ownRows ?? rows.slice(2)
    const put = (l: Law, tuples: E[][]) => {
      const old = instances[l.name] ?? [], arity = 1 + (l.keys?.length ?? 0)
      for (let i = 0; i < old.length; i += arity) tuples.push(old.slice(i, i + arity))
      const unique = [...new Map(tuples.map(tuple => [JSON.stringify(tuple), tuple])).values()]
      instances[l.name] = unique.flat()
    }
    for (const l of family) {
      if ((frameOnly || options.onlySeededPremises) && l !== law) continue
      const keys = [...(l.forall ? [l.forall] : []), ...(l.keys ?? [])]
      let counted = false, columnKey: string | undefined
      walkOnce(l.holds, (node: any) => {
        if (node.op !== 'get') return
        if (m.counts?.[node.map]) counted = true
        const key = node.key
        if (key.op === 'add') {
          const [base, suffix] = key.a.op === 'mul' ? [key.a, key.b] : [key.b, key.a]
          if (base.op === 'mul' && base.k === shape.width && suffix.op === 'var' && keys.includes(suffix.name)) columnKey = suffix.name
        }
      })
      if (counted || !keys.length) continue
      if (keys.length === 1) put(l, rows.map(row => [row]))
      else if (keys.length === 2) put(l, columnKey === keys[1] ? rows.map(row => [row, column]) : rows.flatMap(row => rows.map(other => [row, other])))
      else if (l === law) put(l, frameOnly ? [[a, b, column]] : options.sparseOwn ? [[a, b, column], ...ownRows.flatMap(row => [[row, b, column], [a, row, column]])] : rows.flatMap(row => rows.map(other => [row, other, column])))
    }
    if (!frameOnly) for (const [name, flag] of Object.entries(m.step.flags ?? {})) if (flag.op === 'all' && !flag.keys?.length) instances['?' + name] = [...rows, column]
    if (Object.values(instances).reduce((n, terms) => n + terms.length, 0) > 2048) return
    let packets = countedObligations(m, family, {[law.name]: instances}, index), step = packets.at(-1)
    if (!step) return
    let request = requestFor(step.goal, step.decls)
    if (options.witnessFlags) for (let round = 0; round < 2; round++) {
      const seeded = seedCountWitnessFlags(m, instances, [{decls: step.decls, cert: request}], true)
      if (seeded === instances) break
      Object.assign(instances, seeded)
      if (clock() >= until || pastWall() || Object.values(instances).reduce((n, terms) => n + terms.length, 0) > 2048) return
      packets = countedObligations(m, family, {[law.name]: instances}, index); step = packets.at(-1)
      if (!step) return
      request = requestFor(step.goal, step.decls)
    }
    const goal = mcGoal(step.goal.hyps, step.decls, request)
    if (!goal) return
    const mirror = options.symmetryReuse ? rowSymmetryCache(goal, request, law.forall + '#', law.keys[0]!, until) : undefined
    const close = (path: Path): Tree | undefined => {
      if (clock() >= until || pastWall()) return
      const start = fullWork(), leafEnd = strategyLeafUntil(until, options)
      const reused = mirror?.get(path)
      const fast = !reused && options.fastClosure ? refuteFast(leafConstraints(goal, path)) : undefined
      let scopedTree: Tree | undefined
      if (!reused && fast?.kind !== 'refuted' && options.premiseScoped) {
        const scopedEnd = Math.min(leafEnd, clock() + Math.max(0, leafEnd - clock()) * 3 / 4), seen = new Set<string>()
        for (const guardReads of [false, true]) {
          const scopeStart = fullWork()
          const scoped = countPremiseView(goal, m, law, step.goal.hyps.at(-1)!, step.goal.hyps.slice(0, 2), scopedEnd, guardReads)
          if (!scoped || seen.has(scoped.selected.join(','))) continue
          seen.add(scoped.selected.join(','))
          const attemptEnd = scopedEnd
          const result = growCdcl(scoped.goal, path, {nodes: 0, until: attemptEnd})
          const candidate = 'tree' in result ? rebasePath(scoped.goal, result.tree, path, path, until, goal) : undefined
          scopedTree = candidate && check(goal, candidate, path) ? candidate : undefined
          options.trace?.({query: 'premise-scope', goal: scoped.goal, path: new Map(path), guardReads, outcome: scopedTree ? 'proved' : 'tree' in result ? 'transport-rejected' : result.stuck, hyps: scoped.goal.hyps.length, fullHyps: goal.hyps.length, selected: scoped.selected, omitted: scoped.omitted, allowed: scoped.allowed, scopeUnits: (fullWork() - scopeStart) / fullRate, units: (fullWork() - start) / fullRate})
          if (scopedTree) break
        }
      }
      const result = reused ? {tree: reused} : fast?.kind === 'refuted' ? {tree: {leaf: fast.steps}} : scopedTree ? {tree: scopedTree} : growCdcl(goal, path, {nodes: 0, until: leafEnd})
      const capped = leafEnd < until && clock() >= leafEnd
      const tree = 'tree' in result && check(goal, result.tree, path) && clock() < until ? result.tree : undefined
      if (tree) mirror?.put(path, tree)
      options.observe?.({stage: 'leaf', ...(options.symmetryReuse ? {symmetryEnabled: mirror !== undefined} : {}), method: reused ? 'symmetry' : fast?.kind === 'refuted' ? 'linear' : 'cdcl', outcome: tree ? 'proved' : capped ? 'leaf-cap' : clock() >= until ? 'pool-exhausted' : 'stuck' in result ? result.stuck : 'rejected-proof', goal, path: new Map(path), hyps: goal.hyps.length, units: (fullWork() - start) / fullRate, ...('witness' in result ? {witness: result.witness} : {})})
      return tree
    }
    const split = countGuardTree(until)
    const writtenRows = rowAgreementWrittenKeys(m, shape).slice(0, 4).map(x)
    const finish = (path: Path): Tree | undefined => options.diagonalAlias && writtenRows.some(row => truth(same(a, row), path) === true && truth(same(b, row), path) === true)
      ? split.condition(same(a, b), path, close, close) : close(path)
    // Written-row cases are ordinary exhaustive equality splits. Extra splits
    // only cost work; they cannot establish an invariant or authorize a fact.
    const choose = (i: number, path: Path): Tree | undefined => {
      if (i >= writtenRows.length) return finish(path)
      const written = writtenRows[i]!
      return split.condition(same(a, written), path,
        p => split.condition(same(b, written), p, q => choose(i + 1, q), q => choose(i + 1, q)),
        p => split.condition(same(b, written), p, q => choose(i + 1, q), q => choose(i + 1, q)))
    }
    const run = (path: Path) => options.diagonalFirst ? split.condition(same(a, b), path, close, p => choose(0, p)) : choose(0, path)
    const fixed = options.operationPath ? fixedCountFrameCase(m) : undefined
    const tree = fixed ? split.rows(countFrameConditions(fixed), new Map(), run, path => operationRefutation(leafConstraints(goal, path), fixed.name)) : run(new Map())
    if (!tree) return
    const stepCert: CountCert = {...request, tree}
    if (options.deferToComposition) return {instances, certs: {[step.goal.name]: stepCert}}
    if (!checkMC(step.goal.hyps, step.decls, stepCert)) return
    const certs: Record<string, CountCert> = {[step.goal.name]: stepCert}
    for (const initial of packets.slice(0, -1)) {
      if (clock() >= until || pastWall()) return
      const base = requestFor(initial.goal, initial.decls), initialGoal = mcGoal(initial.goal.hyps, initial.decls, base)
      const result = initialGoal && growCdcl(initialGoal, new Map(), {nodes: 0, until})
      if (!result || !('tree' in result)) return
      const cert: CountCert = {...base, tree: result.tree}
      if (!checkMC(initial.goal.hyps, initial.decls, cert)) return
      certs[initial.goal.name] = cert
    }
    return clock() < until && !pastWall() ? {instances, certs} : undefined
  })
}
