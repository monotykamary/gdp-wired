// Retained laws are untrusted proposals, never machine facts or caller assumptions.
// This operates on an already-normalized machine and its complete public law set.
import type {C, Law, Machine} from './machine.ts'
import {decideLaw, proveLaw, proveSetFast} from '../kernel/prove.ts'

type Closure = ReturnType<typeof proveSetFast>
type Drop = {name: string, goal: string, stuck: 'sat'}
export type SeedResult =
  | {status: 'checked', laws: Law[], kept: Law[], dropped: Drop[], closure: Closure}
  | {status: 'inconclusive', kept: Law[], dropped: Drop[], reason: string}

// The caller must impose the kernel deadline around this call, and must not use
// an inconclusive result as an assumption. In particular, a decision isn't a
// certificate: only the final checked family carries proof authority.
export function proveCandidateSeeds(machine: Machine, publicLaws: Law[], candidates: Law[]): SeedResult {
  if(Object.keys(machine.counts ?? {}).length)
    return {status:'inconclusive',kept:[],dropped:[],reason:'count-bearing machine requires counted candidate admission'}
  const names = new Set<string>()
  for (const law of [...publicLaws, ...candidates]) {
    if (!law.name || names.has(law.name)) throw Error('candidate family requires unique law names')
    names.add(law.name)
  }
  // Witness/ghost transformations need an independently qualified projection.
  // Do not silently treat one as a plain universally quantified law.
  const someKey = (c: C, positive = true): boolean => c.op === 'all' ? (!positive || someKey(c.c, positive)) : c.op === 'not' ? someKey(c.x, !positive) : c.op === 'and' || c.op === 'or' ? c.xs.some(x => someKey(x, positive)) : false
  const supported = new Set(['name', 'holds', 'forall', 'keys'])
  if ([...publicLaws, ...candidates].some(l => Object.keys(l).some(k => !supported.has(k)) || someKey(l.holds)))
    return {status: 'inconclusive', kept: [], dropped: [], reason: 'existential family requires projection'}
  let kept = [...candidates]
  const dropped: Drop[] = []
  for (;;) {
    const family = [...publicLaws, ...kept]
    let removed = false
    for (let i = 0; i < kept.length; i++) {
      const decision = decideLaw(machine, family, publicLaws.length + i) ?? proveLaw(machine, family, publicLaws.length + i)
      if (!decision.proven) {
        if (decision.stuck !== 'sat') return {status: 'inconclusive', kept, dropped, reason: `undecided candidate: ${kept[i]!.name}: ${decision.stuck}`}
        dropped.push({name: kept[i]!.name, goal: decision.goal, stuck: 'sat'})
        kept = kept.filter((_, j) => j !== i)
        removed = true
        break // every previous decision may depend on the dropped law
      }
    }
    if (!removed) break
  }
  const laws = [...publicLaws, ...kept]
  const closure = proveSetFast(machine, laws)
  if (!closure.proven || !closure.checked || !closure.proof)
    return {status: 'inconclusive', kept, dropped, reason: closure.failed?.goal ?? 'whole-family proof not checked'}
  return {status: 'checked', laws, kept, dropped, closure}
}
