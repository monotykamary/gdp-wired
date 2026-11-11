import {expect, test} from 'bun:test'
import {type Law, type Machine, get, n, same, x} from './machine.ts'
import {countsDump, countedAttempts} from './counts.ts'
import {countTierBudget} from './count-tier-budget.ts'
import {clock, counted, fullRate, withBudget} from '../kernel/prove.ts'
import {checkMC, countedObligations} from '../kernel/kernel.ts'

const bounded = (run: (until: number) => void) => counted(fullRate, () => withBudget(10000000, () => run(clock() + 10000)), true)
test('production containment transports a local proof to the full row layout', () => bounded(until => {
 const m: Machine = {name: 'renamable maps', params: [], inputs: [], state: {}, maps: {left: 0, right: 0, unrelated: 0}, step: {maps: {left: {key: n(0), value: get('right', n(0))}, right: {key: n(0), value: get('left', n(0))}}}}
 const owner: Law = {name: 'owner', holds: same(get('left', n(0)), n(0))}, premise: Law = {name: 'premise', holds: same(get('right', n(0)), n(0))}, extra: Law = {name: 'extra', holds: same(get('unrelated', n(0)), n(0))}
 const family = [extra, owner, premise], events: any[] = [], previous = countsDump.on
 countsDump.on = event => events.push(event)
 try {
  const attempts = countedAttempts(m, [owner], new Set([premise]), until, true, true, countTierBudget(clock(), until, 1))
  const result = attempts.traced(owner, family, 0, 1000)
  expect('proof' in result).toBe(true)
  if (!('proof' in result)) return
  expect(events.some(e => e.phase === 'premise-context' && e.outcome === 'proved' && e.local === 2 && e.whole === 3)).toBe(true)
  for (const {goal, decls} of countedObligations(m, family, {[owner.name]: result.proof.instances}, 1)) expect(checkMC(goal.hyps, decls, result.proof.certs[goal.name]!)).toBe(true)
  const changed = [extra, owner, {...premise, holds: same(get('right', n(0)), n(1))}], step = countedObligations(m, changed, {[owner.name]: result.proof.instances}, 1).at(-1)!
  expect(checkMC(step.goal.hyps, step.decls, result.proof.certs[step.goal.name]!)).toBe(false)
 } finally {countsDump.on = previous}
}))
test('production fallback can prove a full goal after its contained local model', () => bounded(until => {
 const m: Machine = {name: 'scalar dependency outside map containment', params: [], inputs: [], state: {left: n(0), right: n(0), extra: n(0)}, step: {state: {left: x('right'), right: x('left')}}}
 const owner: Law = {name: 'left is zero', holds: same(x('left'), n(0))}, premise: Law = {name: 'right is zero', holds: same(x('right'), n(0))}, extra: Law = {name: 'extra', holds: same(x('extra'), n(0))}
 const family = [extra, owner, premise], events: any[] = [], previous = countsDump.on
 countsDump.on = event => events.push(event)
 try {
  const result = countedAttempts(m, [owner], new Set(), until, true, true, countTierBudget(clock(), until, 1)).traced(owner, family, 0, 1000)
  expect('proof' in result).toBe(true)
  expect(events.some(e => e.phase === 'premise-context' && e.outcome === 'declined' && e.local === 1)).toBe(true)
  expect(events.some(e => e.phase === 'premise-context' && e.outcome === 'fallback')).toBe(true)
  if ('proof' in result) for (const {goal, decls} of countedObligations(m, family, {[owner.name]: result.proof.instances}, 1)) expect(checkMC(goal.hyps, decls, result.proof.certs[goal.name]!)).toBe(true)
 } finally {countsDump.on = previous}
}))
