// C projects read by gdp-wired's C front end (core/extract-c.ts): the rules in research/langs/c/rules/ are what the
// extractor printed from each project at its pinned version (each checked against the project's own file, compiled
// beside a generated harness with the undefined-behavior sanitizer trapping: research/langs/c/run.ts), not written by
// hand; the laws are research/langs/c/specs.ts's. Ring-Buffer 8b93e1b: MIT, (c) Anders Kalør. nghttp2 1.70.0: MIT, (c)
// nghttp2 contributors. ENet 1.3.18: MIT, (c) Lee Salzman. Each law is proven with the extracted rule's own invariants
// beside it (each number within its type's range), which the extractor prints with the rule.
import {proveRule, proveSteps} from '../../../core/dsl.ts'
import type {Law} from '../../../core/machine.ts'
import {SPECS} from '../../langs/c/specs.ts'
import {type RealItem, type RealLaw} from '../lib.ts'
import * as rb from '../../langs/c/rules/ring_buffer_t.ts'
import * as ratelim from '../../langs/c/rules/nghttp2_ratelim.ts'
import * as enet from '../../langs/c/rules/ENetPeer_throttle.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyRule = any
const RULES: Record<string, Record<string, unknown>> = {'queue/Ring-Buffer/ring_buffer_t': rb, 'rate limit/nghttp2/nghttp2_ratelim': ratelim, 'rate limit/enet/ENetPeer throttle': enet}
export const items: RealItem[] = SPECS.map(s => {
  const m = RULES[s.id]!
  const r = Object.entries(m).find(([k]) => k.endsWith('Rule'))![1] as AnyRule
  const inv = (Object.entries(m).find(([k]) => k.endsWith('Invariants'))?.[1] ?? []) as Law[]
  const laws: RealLaw[] = s.laws.map(l => ({name: l.name, kind: l.kind, intent: l.intent, why: l.why, form: 'then' in (l.law(r) as object) ? 'step' as const : 'invariant' as const,
    prove: (ms: number) => { const law = l.law(r); return 'then' in (law as object) ? proveSteps(r, inv, [law as never], {search: {ms}}) : proveRule(r, [...inv, law as Law], {search: {ms}}) }}))
  return {id: s.id, domain: s.domain, summary: s.summary, expressible: 'partial' as const, laws,
    source: {repo: s.repo, commit: `${s.project} ${s.version}`, path: s.file, lines: 'the functions named', export: s.reads.split(': ').slice(1).join(': '), licence: s.licence, author: s.author, language: 'C'},
    gaps: [{gap: 'async' as const, blocks: 'part' as const, detail: 'extracted from the code; each call one step (the struct is the caller\'s alone: no other thread touches it), the rule\'s numbers stop at ±2^53'}]}
})
