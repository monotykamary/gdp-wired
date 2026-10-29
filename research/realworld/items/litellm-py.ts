// LiteLLM v1.106.6 (61c6ab78393ef45683dd7d963d2a315bd845e20b), read from its Python by gdp-wired/extract-py: the rules in
// research/langs/litellm/rules/ are what the extractor printed from the code at the pin (each checked against the code
// by running both, research/langs/litellm/run.ts), not written by hand; the laws are research/langs/litellm/specs.ts's.
// MIT, (c) Berri AI. https://github.com/BerriAI/litellm/tree/61c6ab78393ef45683dd7d963d2a315bd845e20b
//
// Unlike the other items, the rule is the code's own: the gaps are what each extraction states about the code around
// it (an answered call, a store), not a modelling choice. Each law is proven with the extracted rule's own invariants
// beside it (what every state of the code is: a map's key it doesn't hold holds the defaults), which the extractor
// prints with the rule.
import {proveSteps} from '../../../core/dsl.ts'
import type {Law} from '../../../core/machine.ts'
import {PIN, SPECS} from '../../langs/litellm/specs.ts'
import {type RealItem, type RealLaw} from '../lib.ts'
import * as key from '../../langs/litellm/rules/virtual_key_max_budget_check.ts'
import * as team from '../../langs/litellm/rules/team_max_budget_check.ts'
import * as project from '../../langs/litellm/rules/project_max_budget_check.ts'
import * as endUser from '../../langs/litellm/rules/check_end_user_budget.ts'
import * as iterations from '../../langs/litellm/rules/MaxIterationsHandler.ts'
import * as session from '../../langs/litellm/rules/MaxBudgetPerSessionHandler.ts'
import * as cooldown from '../../langs/litellm/rules/should_cooldown_based_on_allowed_fails_policy.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyRule = any
const ruleOf = (m: Record<string, unknown>): {r: AnyRule, inv: Law[]} => {
  const r = Object.entries(m).find(([k]) => k.endsWith('Rule'))![1] as AnyRule
  const inv = (Object.entries(m).find(([k]) => k.endsWith('Invariants'))?.[1] ?? []) as Law[]
  return {r, inv}
}
const RULES: Record<string, Record<string, unknown>> = {
  'quota/litellm-py/virtual_key_max_budget_check': key, 'quota/litellm-py/team_max_budget_check': team,
  'quota/litellm-py/_project_max_budget_check': project, 'quota/litellm-py/check_end_user_budget': endUser,
  'rate limit/litellm-py/MaxIterationsHandler': iterations, 'quota/litellm-py/MaxBudgetPerSessionHandler': session,
  'circuit breaker/litellm-py/should_cooldown_based_on_allowed_fails_policy': cooldown,
}
export const items: RealItem[] = SPECS.map(s => {
  const {r, inv} = ruleOf(RULES[s.id]!)
  const [path, ...fns] = s.reads.split(': ')
  const laws: RealLaw[] = s.laws.map(l => ({name: l.name, kind: l.kind, intent: l.intent, why: l.why, form: 'step' as const,
    prove: (ms: number) => proveSteps(r, inv, [l.law(r)], {search: {ms}})}))
  return {
    id: s.id, domain: s.domain, summary: s.summary, expressible: 'partial' as const, laws,
    source: {repo: PIN.repo, commit: PIN.commit, path: path!, lines: 'the functions named', export: fns.join(': '), licence: PIN.licence, author: PIN.author, language: PIN.language},
    gaps: [{gap: 'external' as const, blocks: 'part' as const, detail: `extracted from the code; stated about the rest: ${s.boundary}`}],
  }
})
