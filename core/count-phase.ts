// Optional fixed-operation phase strategy. Discovery is untrusted; all leaves,
// INIT and STEP are checked against the caller's ordinary count obligations.
import {type Law, type Machine, x} from './machine.ts'
import {type CountStrategyOptions, strategyLeafUntil} from './count-strategy.ts'
import {countsForReads} from './count-facts.ts'
import {countFrameConditions, fixedCountFrameCase, ownCountLawInstance} from './count-frames.ts'
import {discoverCountGuardShape} from './count-guard-shape.ts'
import {add, k, scale} from './solver.ts'
import {type CountCert, type CountDecl, type FrameCut, type Goal, type Instances, type MapRead, type Path, type Tree, canon, checkMC, countedObligations, frameOk, framePath, mcGoal} from '../kernel/kernel.ts'
import {clock, grow, pastWall} from '../kernel/prove.ts'
import {growCdcl} from '../kernel/cdcl.ts'
import {countSearchView, proveCountQuery} from './count-query.ts'

export type PhaseCountProof = {instances: Instances, certs: Record<string, CountCert>}
export type CountRequestBuilder = (goal: Goal, declarations: CountDecl[]) => Pick<CountCert, 'reads' | 'insts' | 'picks'>
export function proveFixedCountPhase(m: Machine, family: Law[], law: Law, seed: Instances, until: number, requestFor: CountRequestBuilder, observe?: (stage: string) => void, options: CountStrategyOptions = {}): PhaseCountProof | undefined {
  if (clock() >= until || pastWall() || !family.includes(law)) return
  const shape = discoverCountGuardShape(m, law, family), choice = fixedCountFrameCase(m)
  if (!shape?.phase || !choice) return
  observe?.('shape')
  const instances = {...ownCountLawInstance(law, seed)}
  for (const premise of shape.phase.laws) instances[premise.name] = [x(law.keys![0]!)]
  const packets = countedObligations(m, family, {[law.name]: instances}, family.indexOf(law)), step = packets.at(-1)
  if (!step) return
  const base = requestFor(step.goal, step.decls), counts = countsForReads(step.decls, base.reads)
  if (!counts) return
  const targets = [shape.voteMap, shape.rowMap]
  const post = base.reads.filter(r => r[1].endsWith('#') && targets.includes(r[1].slice(0, -1)))
  const voted = post.find(r => r[1] === shape.voteMap + '#'), row = post.find(r => r[1] === shape.rowMap + '#')
  if (!voted || !row) return
  const before = (read: MapRead) => base.reads.find(r => r[1] === read[1].slice(0, -1) && JSON.stringify(r[2]) === JSON.stringify(read[2]))
  const preVote = before(voted), preRow = before(row), bound = counts.find(c => c.v === voted[0])!.below
  if (!preVote || !preRow) return
  const scope = JSON.stringify([m, family, seed, base.reads]), names: string[] = []
  for (let i = 0; names.length < 3; i++) {const name = `phase$count${i}`; if (!scope.includes(JSON.stringify(name))) names.push(name)}
  const request = {reads: base.reads, insts: [
    {wit: names[0]!, below: bound, terms: [[1, voted[0]] as [number, string]], unit: 0},
    {wit: names[1]!, below: bound, terms: [[1, voted[0]] as [number, string], [-1, preVote[0]] as [number, string]], unit: 0},
    {wit: names[2]!, below: bound, terms: [[1, preRow[0]] as [number, string], [-1, row[0]] as [number, string]], unit: 0}
  ], picks: []}
  const goal = mcGoal(step.goal.hyps, step.decls, request)
  if (!goal) return
  observe?.('encoded-step')
  const frames: FrameCut[] = [], conditions = countFrameConditions(choice), minimal = options.minimalView ? countSearchView(step.goal, step.decls, request) : undefined
  // A genuinely unchanged count has one unconditional frame, not an expanding
  // list of duplicate conditional frames whose row positions vary by leaf.
  for (const read of post) {
    const pre = before(read); if (!pre) continue
    const cut: FrameCut = {post: read[0], pre: pre[0], when: []}
    if (frameOk(counts, cut)) frames.push(cut)
  }
  const ask = (path: Path): Tree | undefined => {
    if (clock() >= until || pastWall()) return
    for (const read of post) {
      const pre = before(read); if (!pre || frames.some(f => f.post === read[0] && f.pre === pre[0] && !f.when.length)) continue
      const cut: FrameCut = {post: read[0], pre: pre[0], when: [...path.values()].map(t => t.holds ? t.lin : add(scale(t.lin, -1), k(1)))}
      if (!frames.some(f => JSON.stringify(f) === JSON.stringify(cut)) && frameOk(counts, cut)) frames.push(cut)
    }
    if (minimal) return proveCountQuery(goal, framePath(frames, [], path), until, {query: 'phase-leaf', minimal, leafUnits: options.leafUnits, trace: options.trace, deferCheck: !!options.deferToComposition})
    const result = growCdcl(goal, framePath(frames, [], path), {nodes: 0, until: strategyLeafUntil(until, options)})
    return 'tree' in result ? result.tree : undefined
  }
  const solve = (i: number, path: Path): Tree | undefined => {
    if (clock() >= until || pastWall()) return
    if (i === conditions.length) return ask(path)
    const split = conditions[i]!, id = canon(split), known = path.get(id)?.holds
    if (known !== undefined) return known ? solve(i + 1, path) : ask(path)
    const yes = solve(i + 1, new Map(path).set(id, {lin: split, holds: true}))
    const no = yes && ask(new Map(path).set(id, {lin: split, holds: false}))
    return yes && no ? {split, yes, no} : undefined
  }
  const split = {[shape.phase.name]: 1}, id = canon(split), yes = solve(0, new Map([[id, {lin: split, holds: true}]]))
  const no = yes && solve(0, new Map([[id, {lin: split, holds: false}]]))
  if (!yes || !no) {observe?.('step-search-failed'); return}
  const cert: CountCert = {...request, frames, tree: {split, yes, no}}
  if (options.deferToComposition) {observe?.('proposed-step'); return clock() < until && !pastWall() ? {instances, certs: {[step.goal.name]: cert}} : undefined}
  if (!checkMC(step.goal.hyps, step.decls, cert)) {observe?.('rejected-step'); return}
  observe?.('checked-step')
  const certs: Record<string, CountCert> = {[step.goal.name]: cert}
  for (const initial of packets.slice(0, -1)) {
    if (clock() >= until || pastWall()) return
    const base = requestFor(initial.goal, initial.decls), counts = countsForReads(initial.decls, base.reads), target = base.reads.find(r => r[1].replace(/#$/, '') === shape.voteMap)
    if (!counts || !target) return
    const request = {reads: base.reads, insts: [{wit: names[0]!, below: counts.find(c => c.v === target[0])!.below, terms: [[1, target[0]] as [number, string]], unit: 0}], picks: []}
    const goal = mcGoal(initial.goal.hyps, initial.decls, request), result = goal && grow(goal, new Map(), {nodes: 0, until: strategyLeafUntil(until, options)})
    if (!result || !('tree' in result)) {observe?.('initial-search-failed'); return}
    const cert: CountCert = {...request, tree: result.tree}
    if (!checkMC(initial.goal.hyps, initial.decls, cert)) return
    certs[initial.goal.name] = cert
  }
  return clock() < until && !pastWall() ? {instances, certs} : undefined
}
