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
    today: () => proveSteps(c.rule, [], c.steps!), frontier: () => inferLaws(c.rule, [], c.steps!),
  } : {
    id: `invariant/${w.domain}/${w.case}: ${w.law}`, track: 'invariant', removed: 'its sibling laws',
    today: () => proveRule(c.rule, [law!]), frontier: () => inferLaws(c.rule, [law!]),
  }
})
export const invariantItems: Item[] = [...synth, ...examples]
