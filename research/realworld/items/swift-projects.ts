// Swift packages read by gdp-wired's Swift front end (core/extract-swift.ts): the rules in research/langs/swift/rules/
// are what the extractor printed from each package at its pinned version (each checked against the package itself:
// built by `swift build` beside the generated harness, in debug, and run request by request: research/langs/swift/run.ts),
// not written by hand; the laws are research/langs/swift/specs.ts's. swift-nio-http2 1.46.0 and swift-nio 2.104.0:
// Apache-2.0, (c) Apple Inc. and the SwiftNIO project authors. Each law is proven with the extracted rule's own
// invariants beside it (each fixed width within its range), which the extractor prints with the rule.
import {proveRule, proveSteps} from '../../../core/dsl.ts'
import type {Law} from '../../../core/machine.ts'
import {SPECS} from '../../langs/swift/specs.ts'
import {type RealItem, type RealLaw} from '../lib.ts'
import * as inbound from '../../langs/swift/rules/InboundWindowManager.ts'
import * as window from '../../langs/swift/rules/HTTP2FlowControlWindow.ts'
import * as watermark from '../../langs/swift/rules/HighLowWatermark.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyRule = any
const RULES: Record<string, Record<string, unknown>> = {'flow control/swift-nio-http2/InboundWindowManager': inbound, 'flow control/swift-nio-http2/HTTP2FlowControlWindow': window, 'backpressure/swift-nio/HighLowWatermark': watermark}
export const items: RealItem[] = SPECS.map(s => {
  const m = RULES[s.id]!
  const r = Object.entries(m).find(([k]) => k.endsWith('Rule'))![1] as AnyRule
  const inv = (Object.entries(m).find(([k]) => k.endsWith('Invariants'))?.[1] ?? []) as Law[]
  const laws: RealLaw[] = s.laws.map(l => ({name: l.name, kind: l.kind, intent: l.intent, why: l.why, form: 'then' in (l.law(r) as object) ? 'step' as const : 'invariant' as const,
    prove: (ms: number) => { const law = l.law(r); return 'then' in (law as object) ? proveSteps(r, inv, [law as never], {search: {ms}}) : proveRule(r, [...inv, law as Law], {search: {ms}}) }}))
  return {id: s.id, domain: s.domain, summary: s.summary, expressible: 'partial' as const, laws,
    source: {repo: s.repo, commit: `${s.project} ${s.version} (${s.tag})`, path: s.file, lines: 'the methods named', export: s.reads.split(': ').slice(1).join(': '), licence: s.licence, author: s.author, language: 'Swift'},
    gaps: [{gap: 'async' as const, blocks: 'part' as const, detail: 'extracted from the code; each call one step (a struct\'s mutating methods, with no suspension point), the rule\'s numbers stop at ±2^53'}]}
})
