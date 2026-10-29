// Ruby gems read by gdp-wired's Ruby front end (core/extract-rb.ts): the rules in research/langs/ruby/rules/ are what
// the extractor printed from each gem at its pinned version (each checked against the gem's own file, run beside
// core/rb/harness.rb: research/langs/ruby/run.ts), not written by hand; the laws are research/langs/ruby/specs.ts's.
// semian 0.28.4: MIT, (c) Shopify. stoplight 6.0.0: MIT, (c) Cameron Desautels, Taylor Fausak, Tëma Bolshakov.
// Each law is proven with the extracted rule's own invariants beside it (a nil field holding 0), which the extractor
// prints with the rule.
import {proveRule, proveSteps} from '../../../core/dsl.ts'
import type {Law} from '../../../core/machine.ts'
import {SPECS} from '../../langs/ruby/specs.ts'
import {type RealItem, type RealLaw} from '../lib.ts'
import * as state from '../../langs/ruby/rules/Simple_State.ts'
import * as int from '../../langs/ruby/rules/Simple_Integer.ts'
import * as light from '../../langs/ruby/rules/Memory_Storage_State.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyRule = any
const RULES: Record<string, Record<string, unknown>> = {'circuit breaker/semian/Simple::State': state, 'circuit breaker/semian/Simple::Integer': int, 'circuit breaker/stoplight/Memory::Storage::State': light}
export const items: RealItem[] = SPECS.map(s => {
  const m = RULES[s.id]!
  const r = Object.entries(m).find(([k]) => k.endsWith('Rule'))![1] as AnyRule
  const inv = (Object.entries(m).find(([k]) => k.endsWith('Invariants'))?.[1] ?? []) as Law[]
  const laws: RealLaw[] = s.laws.map(l => ({name: l.name, kind: l.kind, intent: l.intent, why: l.why, form: 'then' in (l.law(r) as object) ? 'step' as const : 'invariant' as const,
    prove: (ms: number) => { const law = l.law(r); return 'then' in (law as object) ? proveSteps(r, inv, [law as never], {search: {ms}}) : proveRule(r, [...inv, law as Law], {search: {ms}}) }}))
  return {id: s.id, domain: s.domain, summary: s.summary, expressible: 'partial' as const, laws,
    source: {repo: s.repo, commit: `${s.gem} ${s.version} (rubygems.org)`, path: s.file, lines: 'the methods named', export: s.reads.split(': ').slice(1).join(': '), licence: s.licence, author: s.author, language: 'Ruby'},
    gaps: [{gap: 'async' as const, blocks: 'part' as const, detail: 'extracted from the code; each call one step (a mutex\'s synchronize makes it atomic; the clock read as the request\'s time, at whole seconds)'}]}
})
