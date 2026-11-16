import {describe, expect, test} from 'bun:test'
import {proveCandidateSeeds} from '../../core/candidate-seeds.ts'
import type {E, Law, Machine} from '../../core/machine.ts'
import {proofOutput, publishProof, type PublicProofOutput} from '../../core/proof-output.ts'
import {rule, proveRule} from '../../core/dsl.ts'
import {checkGhostedLaws, someOfGhostsOk, type Ghosted} from '../../kernel/kernel.ts'

const n = (value: number): E => ({op: 'const', value})
const v = (name: string): E => ({op: 'var', name})
const machine: Machine = {name: 'witness', params: [], inputs: [], state: {x: n(0)}, step: {state: {x: n(0)}}}
const publicLaw: Law = {name: 'a value exists', some: ['w'], holds: {op: '=', a: v('w'), b: v('x')}}
const bad: Law = {name: 'bad seed', holds: {op: '=', a: v('x'), b: n(1)}}

describe('existential candidate admission', () => {
  test('checks a fixed term and drops false helpers, preserving the public object', () => {
    const out = proveCandidateSeeds(machine, [publicLaw], [bad], {[publicLaw.name]: {terms: {w: v('x')}}})
    expect(out.status).toBe('checked')
    if (out.status !== 'checked') return
    expect(out.laws[0]).toBe(publicLaw)
    expect(out.kept).toEqual([])
    expect(out.dropped.map(d => d.name)).toEqual([bad.name])
    expect(out.closure.checked).toBe(true)
    expect(out.projection).toBe('skolem')
  })
  test('does not trust a missing or tampered witness', () => {
    expect(proveCandidateSeeds(machine, [publicLaw], []).status).toBe('inconclusive')
    expect(proveCandidateSeeds(machine, [publicLaw], [], {[publicLaw.name]: {terms: {w: n(1)}}}).status).toBe('inconclusive')
    expect(proveCandidateSeeds(machine, [publicLaw], [], {[publicLaw.name]: {terms: {}}}).status).toBe('inconclusive')
    expect(proveCandidateSeeds(machine, [publicLaw], [], {[publicLaw.name]: {terms: {w: n(0), extra: n(0)}}}).status).toBe('inconclusive')
    expect(proveCandidateSeeds(machine, [publicLaw], [], {unknown: {terms: {w: n(0)}}}).status).toBe('inconclusive')
    expect(() => proveCandidateSeeds(machine, [publicLaw], [publicLaw])).toThrow()
  })
  test('never projects an ordinary public law that reads a new ghost', () => {
    const ordinary: Law = {name: 'ghost is zero', holds: {op: '=', a: v('g'), b: n(0)}}
    expect(proveCandidateSeeds(machine, [ordinary], [], {}, {vars: {g: {start: n(0), step: n(0)}}, maps: {}}).status).toBe('inconclusive')
    expect(proveCandidateSeeds(machine, [{...ordinary, stated: ordinary.holds}], []).status).toBe('inconclusive')
  })
  test('checks a proposed ghost against the unchanged source and retains projection provenance', () => {
    let observed: unknown
    proofOutput.on = e => { observed = e.proof }
    try {
      const ghosts = {vars: {g: {start: n(0), step: n(0)}}, maps: {}}
      const out = proveCandidateSeeds(machine, [publicLaw], [], {[publicLaw.name]: {terms: {w: v('g')}}}, ghosts)
      expect(out.status).toBe('checked')
      if (out.status !== 'checked') return
      publishProof(out.closure, machine, [publicLaw])
      expect(observed).toMatchObject({kind: 'derived', context: {kind: 'skolem', original: machine, laws: [publicLaw]}})
      expect(proveCandidateSeeds(machine, [publicLaw], [], {[publicLaw.name]: {terms: {w: v('g')}}}, {vars: {x: {start: n(0), step: n(0)}}, maps: {}}).status).toBe('inconclusive')
    } finally { proofOutput.on = undefined }
  })
})


test('public proveRule retains and checks the full point-ghost projection', () => {
  const r = rule('public existential seed').state({x: 0}).step(() => ({x: 0}))
  const goal: Law = {name: 'every key has zero witness', forall: 'k', some: ['w'], holds: {op: '=', a: v('w'), b: v('x')}}
  const good: Law = {name: 'x stays zero', holds: {op: '=', a: v('x'), b: n(0)}}
  const wrong: Law = {name: 'bad candidate', holds: {op: '=', a: v('x'), b: n(1)}}
  const terms = {w: {op: 'get', map: 'G', key: v('k')} as E}
  const ghosts = {vars: {}, maps: {G: {start: 0, write: {key: n(0), value: n(0)}}}}
  const events: PublicProofOutput[] = [], audits: {status: string, dropped: {name: string}[]}[] = []
  const prior = proofOutput.on
  try {
    proofOutput.on = e => events.push(e)
    const result = proveRule(r as never, [goal], {search: true, candidateSeeds: {laws: [good, wrong], witnesses: {[goal.name]: {terms}}, ghosts, report: a => audits.push(a)}})
    expect(result.proven && result.checked).toBe(true)
    expect(audits[0]).toMatchObject({status: 'checked'})
    expect(audits[0]?.dropped.map(d => d.name)).toContain(wrong.name)
    expect(events[0]?.original.laws[0]).toBe(goal)
    let node = events[0]?.proof
    while (node?.kind === 'derived' && (node.context as {kind?: string})?.kind !== 'skolem') node = node.parents[0]
    expect(node?.kind).toBe('derived')
    if (!node || node.kind !== 'derived') throw Error('missing skolem receipt')
    const ctx = node.context as {original: Machine, laws: Law[], G: Ghosted, plains: Record<string, {plain: Law, sub: Record<string, E>}>, family: Law[]}
    expect(ctx.original).toEqual(events[0]!.original.machine)
    expect(ctx.laws.find(l => l.name === goal.name)).toBe(goal)
    const leaf = node.parents[0]
    expect(leaf?.kind).toBe('usual')
    if (!leaf || leaf.kind !== 'usual') throw Error('missing checked family')
    expect(ctx.family.map(l => l.name)).toContain(good.name)
    expect(checkGhostedLaws(ctx.G, ctx.family, leaf.proof)).toBe(true)
    expect(someOfGhostsOk(ctx.G, goal, ctx.plains[goal.name]!.plain, ctx.plains[goal.name]!.sub)).toBe(true)
    const badGhosts = {vars: {}, maps: {G: {start: 0, write: {key: n(0), value: n(1)}}}}
    expect(proveCandidateSeeds(r.machine, [goal], [], {[goal.name]: {terms}}, badGhosts).status).toBe('inconclusive')
    const falseGoal: Law = {...goal, holds: {op: 'and', xs: [goal.holds, {op: '=', a: v('x'), b: n(1)}]}}
    const rejected = proveRule(r as never, [falseGoal], {search: true, candidateSeeds: {laws: [], witnesses: {[goal.name]: {terms: {w: n(1)}}}, ghosts: badGhosts}})
    expect(rejected.proven && rejected.checked).toBe(false)
  } finally { proofOutput.on = prior }
})
