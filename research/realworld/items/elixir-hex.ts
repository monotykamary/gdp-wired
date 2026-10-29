// Elixir packages read by gdp-wired's Elixir front end (core/extract-ex.ts): the rules in research/langs/elixir/rules/
// are what the extractor printed from each package at its pinned version (each checked against the package's own
// module, compiled and run beside core/ex/harness.exs: research/langs/elixir/run.ts), not written by hand; the laws
// are research/langs/elixir/specs.ts's. ex_break 0.0.9: MIT, (c) 2018 Jonathan Clem. Each law is proven with the
// extracted rule's own invariants beside it (a nil field holding 0), which the extractor prints with the rule.
import {proveRule, proveSteps} from '../../../core/dsl.ts'
import type {Law} from '../../../core/machine.ts'
import {SPECS} from '../../langs/elixir/specs.ts'
import {type RealItem, type RealLaw} from '../lib.ts'
import * as breaker from '../../langs/elixir/rules/Breaker.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyRule = any
const RULES: Record<string, Record<string, unknown>> = {'circuit breaker/ex_break/Breaker': breaker}
export const items: RealItem[] = SPECS.map(s => {
  const m = RULES[s.id]!
  const r = Object.entries(m).find(([k]) => k.endsWith('Rule'))![1] as AnyRule
  const inv = (Object.entries(m).find(([k]) => k.endsWith('Invariants'))?.[1] ?? []) as Law[]
  const laws: RealLaw[] = s.laws.map(l => ({name: l.name, kind: l.kind, intent: l.intent, why: l.why, form: 'then' in (l.law(r) as object) ? 'step' as const : 'invariant' as const,
    prove: (ms: number) => { const law = l.law(r); return 'then' in (law as object) ? proveSteps(r, inv, [law as never], {search: {ms}}) : proveRule(r, [...inv, law as Law], {search: {ms}}) }}))
  return {id: s.id, domain: s.domain, summary: s.summary, expressible: 'partial' as const, laws,
    source: {repo: s.repo, commit: `${s.pkg} ${s.version} (hex.pm)`, path: s.file, lines: 'the functions named', export: s.reads.split(': ').slice(1).join(': '), licence: s.licence, author: s.author, language: 'Elixir'},
    gaps: [{gap: 'async' as const, blocks: 'part' as const, detail: 'extracted from the code; each call one step (an Agent serializes its updates; the clock read as the request\'s time, at whole seconds)'}]}
})
