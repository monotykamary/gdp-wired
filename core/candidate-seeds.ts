// Retained laws, witness terms and ghost definitions are proposals, never facts.
import {walk, type C, type Law, type Machine, type SomeWitness} from './machine.ts'
import {decideLaw, proveLaw, proveSetFast} from '../kernel/prove.ts'
import {type Ghosted, checkGhostedLaws, ghostedMachine, ghostedOk, someOfGhostsOk, substC} from '../kernel/kernel.ts'
import {retainFrom} from './proof-output.ts'

type Closure = ReturnType<typeof proveSetFast>
type Drop = {name: string, goal: string, stuck: 'sat'}
export type SeedGhosts = Pick<Ghosted, 'vars' | 'maps'>
export type SeedResult =
  | {status: 'checked', laws: Law[], kept: Law[], dropped: Drop[], closure: Closure, projection?: 'skolem'}
  | {status: 'inconclusive', kept: Law[], dropped: Drop[], reason: string}

// The caller imposes the deadline. Only the complete checked family is evidence.
// In particular neither a witness nor a ghost definition is a caller assumption.
export function proveCandidateSeeds(machine: Machine, publicLaws: Law[], candidates: Law[], witnesses: Record<string, SomeWitness> = {}, ghosts: SeedGhosts = {vars: {}, maps: {}}): SeedResult {
  const refuse = (reason: string): SeedResult => ({status: 'inconclusive', kept: [], dropped: [], reason})
  if (Object.keys(machine.counts ?? {}).length) return refuse('count-bearing machine requires counted candidate admission')
  const names = new Set<string>()
  for (const law of [...publicLaws, ...candidates]) {
    if (!law.name || names.has(law.name)) throw Error('candidate family requires unique law names')
    names.add(law.name)
  }
  const someKey = (c: C, positive = true): boolean => c.op === 'all' ? (!positive || someKey(c.c, positive)) : c.op === 'not' ? someKey(c.x, !positive) : c.op === 'and' || c.op === 'or' ? c.xs.some(x => someKey(x, positive)) : false
  const supported = new Set(['name', 'holds', 'forall', 'keys'])
  const publicSupported = new Set([...supported, 'some', 'witness'])
  if (candidates.some(l => Object.keys(l).some(k => !supported.has(k)) || someKey(l.holds)) ||
      publicLaws.some(l => Object.keys(l).some(k => !publicSupported.has(k)) || someKey(l.holds)))
    return refuse('existential family requires projection')

  if (Object.keys(witnesses).some(name => !publicLaws.some(l => l.name === name && l.some?.length)))
    return refuse('witness provided for unknown existential law')
  const projecting = publicLaws.some(l => l.some?.length) || Object.keys(ghosts.vars).length > 0 || Object.keys(ghosts.maps).length > 0
  const G: Ghosted = {orig: machine, vars: ghosts.vars, maps: ghosts.maps}
  const gv = new Set(Object.keys(G.vars)), gm = new Set(Object.keys(G.maps))
  const reserved = new Set([...machine.params, ...machine.inputs, ...Object.keys(machine.state), ...Object.keys(machine.maps ?? {}),
    ...(machine.inputMaps ?? []), ...Object.keys(machine.fns ?? {}), ...Object.keys(machine.step.flags ?? {})])
  if ([...gv, ...gm].some(n => reserved.has(n)) || [...gv].some(n => gm.has(n))) return refuse('ghost name collision')
  let publicReadsGhost = false
  for (const law of publicLaws) walk(law.holds, o => {
    if (o.op === 'var' && gv.has(o.name as string) || o.op === 'get' && gm.has(o.map as string) ||
        o.op === 'flag' && gv.has(`?${o.name as string}`)) publicReadsGhost = true
  })
  if (publicReadsGhost) return refuse('public law reads a proposed ghost')
  if (projecting && !ghostedOk(G)) return refuse('ghost definitions not qualified')
  const plains: Record<string, {plain: Law, sub: Record<string, import('./machine.ts').E>}> = Object.create(null)
  const plainPublic: Law[] = []
  for (const law of publicLaws) {
    if (!law.some?.length) { plainPublic.push(law); continue }
    const w = witnesses[law.name]
    const sub = w?.terms
    if (!sub || w.ghost || Object.keys(sub).length !== law.some.length || !law.some.every(n => Object.hasOwn(sub, n)))
      return refuse(`complete witness terms required for ${law.name}`)
    const plain: Law = {name: law.name, holds: substC(law.holds, {vars: Object.assign(Object.create(null), sub), maps: {}, flags: {}}),
      ...(law.forall ? {forall: law.forall} : {}), ...(law.keys ? {keys: law.keys} : {})}
    if (!someOfGhostsOk(G, law, plain, sub)) return refuse(`existential projection not qualified: ${law.name}`)
    plains[law.name] = {plain, sub}
    plainPublic.push(plain)
  }
  const working = projecting ? ghostedMachine(G) : machine
  let kept = [...candidates]
  const dropped: Drop[] = []
  for (;;) {
    const family = [...plainPublic, ...kept]
    let removed = false
    for (let i = 0; i < kept.length; i++) {
      const decision = decideLaw(working, family, plainPublic.length + i) ?? proveLaw(working, family, plainPublic.length + i)
      if (!decision.proven) {
        if (decision.stuck !== 'sat') return {status: 'inconclusive', kept, dropped, reason: `undecided candidate: ${kept[i]!.name}: ${decision.stuck}${'why' in decision && decision.why ? `: ${decision.why}` : ''}`}
        dropped.push({name: kept[i]!.name, goal: decision.goal, stuck: 'sat'})
        kept = kept.filter((_, j) => j !== i)
        removed = true
        break
      }
    }
    if (!removed) break
  }
  const family = [...plainPublic, ...kept]
  const whole = proveSetFast(working, family)
  if (!whole.proven || !whole.checked || !whole.proof)
    return {status: 'inconclusive', kept, dropped, reason: whole.failed?.goal ?? 'whole-family proof not checked'}
  if (projecting && !checkGhostedLaws(G, family, whole.proof))
    return {status: 'inconclusive', kept, dropped, reason: 'ghosted whole-family proof not checked'}
  const closure = projecting ? retainFrom({...whole}, [whole], {kind: 'skolem', original: machine, laws: publicLaws, G, plains, family}) : whole
  return {status: 'checked', laws: [...publicLaws, ...kept], kept, dropped, closure, ...(projecting ? {projection: 'skolem' as const} : {})}
}
