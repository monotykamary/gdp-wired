import {expect, test} from 'bun:test'
import {type Law, type Machine, get, n, same, x} from './machine.ts'
import {certFor} from './counts.ts'
import {finishCountStrategy, strategyLeafUnits, strategyLeafUntil} from './count-strategy.ts'
import {checkMC, countedObligations, mcGoal} from '../kernel/kernel.ts'
import {clock, counted, fullRate, grow} from '../kernel/prove.ts'

test('a search leaf is one one-hundred-twentieth of the original work allowance', () => {
  for (const work of [0, 120, 6000, 48000, 60000, 120000]) expect(strategyLeafUnits(work)).toBe(work / 120)
  for (const work of [-1, NaN, Infinity]) expect(() => strategyLeafUnits(work)).toThrow(RangeError)
  counted(fullRate, () => {
    const now = clock(), until = now + 1000
    expect(strategyLeafUntil(until, {leafUnits: strategyLeafUnits(60000)})).toBe(now + 500)
    expect(strategyLeafUntil(now + 30, {leafUnits: strategyLeafUnits(60000)})).toBe(now + 30)
  }, true)
})

test('standalone INIT uses the pool even when search leaves have no allowance', () => counted(fullRate, () => {
  const m: Machine = {name: 'renamed zero-count frame', params: [], inputs: [], state: {}, maps: {tokens: 0}, step: {}, counts: {
    total: {j: 'row', key: 'member', below: n(1), body: {op: 'if', c: same(get('tokens', x('member')), n(1)), then: n(1), else: n(0)}}
  }}
  const law: Law = {name: 'natural count', forall: 'r', holds: {op: '<=', a: n(0), b: get('total', x('r'))}}, family = [law], instances = {[law.name]: [x('r#')]}
  const until = clock() + 1000, packets = countedObligations(m, family, {[law.name]: instances}, 0), step = packets.at(-1)!
  const request = certFor(step.goal, step.decls, false, 0), goal = mcGoal(step.goal.hyps, step.decls, request)!, result = grow(goal, new Map(), {nodes: 0, until})
  expect('tree' in result).toBe(true)
  if (!('tree' in result)) return
  const stages: string[] = []
  const proof = finishCountStrategy(m, family, law, instances, 'total', {...request, tree: result.tree}, until,
    (g, ds) => certFor(g, ds, false, 0), (stage, checked) => {if (checked) stages.push(stage)}, {leafUnits: 0})
  expect(proof).toBeDefined()
  expect(stages).toContain('initial-check')
  if (proof) for (const packet of packets) expect(checkMC(packet.goal.hyps, packet.decls, proof.certs[packet.goal.name]!)).toBe(true)
}, true))
