// Rust crates read by gdp-wired's Rust front end (core/extract-rs.ts): the rules in research/langs/rust/rules/ are what
// the extractor printed from each crate at its pinned version (each checked against the crate's own code, built with
// cargo beside a generated harness: research/langs/rust/run.ts), not written by hand; the laws are
// research/langs/rust/specs.ts's. gcra 0.6.0: MIT, (c) Sam Shih. circuitbreaker-rs 0.1.1: MIT OR Apache-2.0.
// Each law is proven with the extracted rule's own invariants beside it (each fixed-width field within its type's
// range, a None one holding 0), which the extractor prints with the rule.
import {proveRule, proveSteps} from '../../../core/dsl.ts'
import type {Law} from '../../../core/machine.ts'
import {SPECS} from '../../langs/rust/specs.ts'
import {type RealItem, type RealLaw} from '../lib.ts'
import * as gcra from '../../langs/rust/rules/GcraState.ts'
import * as cb from '../../langs/rust/rules/StateManager.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyRule = any
const RULES: Record<string, Record<string, unknown>> = {'rate limit/gcra/GcraState': gcra, 'circuit breaker/circuitbreaker-rs/StateManager': cb}
export const items: RealItem[] = SPECS.map(s => {
  const m = RULES[s.id]!
  const r = Object.entries(m).find(([k]) => k.endsWith('Rule'))![1] as AnyRule
  const inv = (Object.entries(m).find(([k]) => k.endsWith('Invariants'))?.[1] ?? []) as Law[]
  const laws: RealLaw[] = s.laws.map(l => ({name: l.name, kind: l.kind, intent: l.intent, why: l.why, form: 'then' in (l.law(r) as object) ? 'step' as const : 'invariant' as const,
    prove: (ms: number) => { const law = l.law(r); return 'then' in (law as object) ? proveSteps(r, inv, [law as never], {search: {ms}}) : proveRule(r, [...inv, law as Law], {search: {ms}}) }}))
  const [path, ...rest] = s.reads.split(': ')
  return {id: s.id, domain: s.domain, summary: s.summary, expressible: 'partial' as const, laws,
    source: {repo: s.repo, commit: `${s.crate} ${s.version} (crates.io)`, path: path!, lines: 'the functions named', export: rest.join(': '), licence: s.licence, author: s.author, language: 'Rust'},
    gaps: [{gap: 'async' as const, blocks: 'part' as const, detail: 'extracted from the code; each call one step (the atomics and the lock read as the fields they are: the claim is for calls that do not interleave)'}]}
})
