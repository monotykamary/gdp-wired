// Java and Kotlin projects read by gdp-wired's JVM front ends (core/extract-jvm.ts): the rules in
// research/langs/jvm/rules/ are what the extractor printed from each project at its pinned version (each checked against
// the project's own code: compiled from the file with javac or kotlinc, or loaded from the release's jar, and run by
// core/jvm/Harness.java: research/langs/jvm/run.ts), not written by hand; the laws are research/langs/jvm/specs.ts's.
// grpc-java 1.85.1: Apache-2.0, (c) The gRPC Authors. resilience4j 2.4.0: Apache-2.0, (c) Robert Winkler and Bohdan
// Storozhuk. OkHttp 5.5.1: Apache-2.0, (c) Square, Inc. Arrow 2.3.0.1: Apache-2.0, (c) The Arrow Authors. Each law is
// proven with the extracted rule's own invariants beside it (each int within its type's range), which the extractor
// prints with the rule.
import {proveRule, proveSteps} from '../../../core/dsl.ts'
import type {Law} from '../../../core/machine.ts'
import {SPECS} from '../../langs/jvm/specs.ts'
import {type RealItem, type RealLaw} from '../lib.ts'
import * as throttle from '../../langs/jvm/rules/RetriableStream_Throttle.ts'
import * as partial from '../../langs/jvm/rules/PartialAggregation.ts'
import * as window from '../../langs/jvm/rules/WindowCounter.ts'
import * as count from '../../langs/jvm/rules/OpeningStrategy_Count.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyRule = any
const RULES: Record<string, Record<string, unknown>> = {'rate limit/grpc-java/RetriableStream.Throttle': throttle, 'circuit breaker/resilience4j/PartialAggregation': partial, 'rate limit/okhttp/WindowCounter': window, 'circuit breaker/arrow/OpeningStrategy.Count': count}
export const items: RealItem[] = SPECS.map(s => {
  const m = RULES[s.id]!
  const r = Object.entries(m).find(([k]) => k.endsWith('Rule'))![1] as AnyRule
  const inv = (Object.entries(m).find(([k]) => k.endsWith('Invariants'))?.[1] ?? []) as Law[]
  const laws: RealLaw[] = s.laws.map(l => ({name: l.name, kind: l.kind, intent: l.intent, why: l.why, form: 'then' in (l.law(r) as object) ? 'step' as const : 'invariant' as const,
    prove: (ms: number) => { const law = l.law(r); return 'then' in (law as object) ? proveSteps(r, inv, [law as never], {search: {ms}}) : proveRule(r, [...inv, law as Law], {search: {ms}}) }}))
  return {id: s.id, domain: s.domain, summary: s.summary, expressible: 'partial' as const, laws,
    source: {repo: s.repo, commit: `${s.project} ${s.version} (${s.tag})`, path: s.files[0]!, lines: 'the methods named', export: s.reads.split(': ').slice(1).join(': '), licence: s.licence, author: s.author, language: s.lang === 'java' ? 'Java' : 'Kotlin'},
    gaps: [{gap: 'async' as const, blocks: 'part' as const, detail: 'extracted from the code; each call one step (a lock or @Synchronized makes it atomic; a compare-and-set loop read as its first pass: the claim is for calls that don\'t interleave), the rule\'s numbers stop at ±2^53'}]}
})
