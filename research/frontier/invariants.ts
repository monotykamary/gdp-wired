// The invariant track's items: research/synth's machines with the law alone, and every law of an example rule that
// isn't proven without its sibling laws (walls.json, from extract.ts), each beside core/infer.ts's search.
import {type Item} from './corpus.ts'
import {type Verdict, proveRule, proveSteps} from '../../core/dsl.ts'
import {proveLaws} from '../../kernel/prove.ts'
import {inferLaws} from '../../core/infer.ts'
import {invariantCases} from '../synth/models.ts'
import {domains} from '../../examples/index.ts'
import type {Wall} from './extract.ts'
import walls from './walls.json'
import {pairs, pairsLaw} from '../../examples/arith.ts'
import {bool, rule, when} from '../../core/dsl.ts'

const machineVerdict = (out: ReturnType<typeof proveLaws>): Verdict => ({proven: out.proven, checked: out.checked, ...(out.failed ? {goal: out.failed.goal, stuck: out.failed.stuck} : {})})
const synth: Item[] = invariantCases.map(c => ({
  id: `invariant/${c.m.name}`, track: 'invariant', removed: 'the inductive invariant the law needs',
  today: () => machineVerdict(proveLaws(c.m, [c.goal])),
  frontier: () => inferLaws(c.m, [c.goal]),
}))
const examples: Item[] = (walls as Wall[]).map(w => {
  const c = domains.find(d => d.domain === w.domain)!.cases.find(k => k.name === w.case)!
  if (c.kind !== 'rule') throw new Error(`${w.case} is not a rule`)
  const law = c.laws.find(l => l.name === w.law)
  return w.steps ? {
    id: `invariant/${w.domain}/${w.case}: step laws`, track: 'invariant', removed: 'the laws the step laws assume',
    today: () => proveSteps(c.rule, [], c.steps!, {search: false}), frontier: () => inferLaws(c.rule, [], c.steps!),
  } : {
    id: `invariant/${w.domain}/${w.case}: ${w.law}`, track: 'invariant', removed: 'its sibling laws',
    today: () => proveRule(c.rule, [law!], {search: false}), frontier: () => inferLaws(c.rule, [law!]),
  }
})
// Remainders nobody wrote (core/infer.ts's remainder candidates): a dispenser that hands out tickets two at a time is
// never at 7 (needs issued mod 2 = 0), its odd refill broken; two counters that each step by two never sum to 10
// (needs (a + b) mod 2 = 1).
const byTwo = () => rule('two counters by two').inputs({first: bool}).state({a: 0, b: 1}).step(({first, a, b}) => ({a: when(first, a.plus(2), a), b: when(first, b, b.plus(2))}))
const remainders: Item[] = [
  ...([[undefined, 'invariant/remainder/pair dispenser: never 7'], ['odd refill', 'invariant/remainder/pair dispenser (odd refill): never 7']] as const).map(([bug, id]): Item => ({
    id, track: 'invariant', removed: 'issued mod 2 = 0', ...(bug ? {broken: 'invariant/remainder/pair dispenser: never 7'} : {}),
    today: () => { const r = pairs(bug); return proveRule(r, [pairsLaw(r)], {search: false}) }, frontier: () => { const r = pairs(bug); return inferLaws(r, [pairsLaw(r)]) }})),
  {id: 'invariant/remainder/two counters by two: never sum to 10', track: 'invariant', removed: '(a + b) mod 2 = 1',
    today: () => { const r = byTwo(); return proveRule(r, [r.law('a + b is never 10', ({a, b}) => a.plus(b).eq(10).not())], {search: false}) },
    frontier: () => { const r = byTwo(); return inferLaws(r, [r.law('a + b is never 10', ({a, b}) => a.plus(b).eq(10).not())]) }},
]
export const invariantItems: Item[] = [...synth, ...examples, ...remainders]
