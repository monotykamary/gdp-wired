// The real-world corpus's item format (README.md): real state machines and business rules from open-source code,
// each written as a gdp-wired rule that mirrors the code's params, inputs, state and step, with the laws a reviewer
// would ask about. Each law is proven with nothing stated beyond the rule and the law itself: `proveRule` /
// `proveSteps` with the default search at a budget of `ms` (60 s in the scored run), `proveLeadsTo` with no rank given
// (the search finds one), `proveDecision` for a claim about one request, within `ms` too.
import {type Liveness, type StepLaw, type Verdict, proveDecision, proveLeadsTo, proveRule, proveSteps} from '../../core/dsl.ts'
import type {Law} from '../../core/machine.ts'

type AnyRule = Parameters<typeof proveRule>[0]
type AnyDecision = Parameters<typeof proveDecision>[0]
// A chart (core/chart.ts) as the corpus reads it: its plain rule and its structural laws (each history one of its own
// states), which `chart.prove` always adds and which state nothing about the code.
type AnyChart = {rule: AnyRule, chartLaws(): Law[]}

export type Domain =
  | 'rate limit' // rate limiters and token buckets
  | 'quota' // quotas and budgets
  | 'ledger' // ledgers, wallets and escrow
  | 'payment' // payment and order state machines
  | 'auth' // auth, session and OAuth flows, refresh-token rotation
  | 'access' // RBAC, ABAC and entitlement checks
  | 'xstate' // XState machines from real apps
  | 'queue' // job queues and retries
  | 'circuit breaker'
  | 'feature flag' // feature flags with rollouts
  | 'inventory' // inventory and reservations
  | 'approval' // multi-step approval workflows
  | 'concurrency' // semaphores, locks and permits

// Where the code is: the repo (owner/name on GitHub, or a URL), the commit it was read at, the file, the lines the
// rule mirrors, the function, class or export, its licence (SPDX) and author (the repo's owner or the file's author).
export type Source = {repo: string, commit: string, path: string, lines: string, export: string, licence: string, author: string, language: string}

// What kind of claim: safety (an invariant: never past the cap), liveness (every pending request resolves), access
// (only an owner can ...), step (one step: a refund only after a capture).
export type LawKind = 'safety' | 'liveness' | 'access' | 'step'
// Where the law's intent comes from: the code's docs (README, doc comment), its tests, or inferred from its obvious
// purpose (`why` says what it was inferred from).
export type Intent = 'docs' | 'tests' | 'inferred'

export type RealLaw = {
  name: string
  kind: LawKind
  intent: Intent
  why: string // the doc or test line it comes from (quoted, short), or what the intent was inferred from
  prove: (ms: number) => Verdict
  // How it is proven (set by the helpers): a decision's `sat` with a witness is a counterexample request, a refutation.
  form?: 'invariant' | 'step' | 'leadsTo' | 'decision'
  live?: {r: AnyRule, l: Liveness} // a liveness law's rule and claim, for diagnostics (rank0.ts)
}

// A language gap: what of the code the rule could not say as the code does it. `gap` is a short key from GAPS (so the
// README can rank them), `detail` the exact thing. `blocks`: 'item' (nothing of the item could be written), 'law' (the
// laws named could not be stated), 'part' (a part of the step is approximated; the item isn't fully expressible).
export type Gap = {gap: Gap_, blocks: 'item' | 'law' | 'part', detail: string, laws?: string[]}
export const GAPS = {
  'float': 'non-integer arithmetic: binary floating point (Math.floor of a float, a rate in tokens per ms), or decimals of unbounded precision (BigNumber quantities)',
  'nonlinear': 'a product of two unknowns the prover does not decide (rate × elapsed time)',
  'division': 'division or remainder by a value that is not a constant',
  'string': 'strings compared other than for equality: globs, regexes, prefixes, parsing',
  'hash': 'a hash function (murmurhash, sha) the rule can only take as an uninterpreted input',
  'unbounded-collection': 'a collection read in ways maps, sets and logs do not give (sorting, min over a list, nested scans)',
  'async': 'concurrency, promises, timers or events firing on their own (a timeout, an interval)',
  'time': 'wall-clock time read inside the step (Date.now()) rather than sent in with the request',
  'recursion': 'recursion over a structure the rule would need a lemma about (role inheritance to any depth)',
  'dynamic-policy': 'a policy that is data loaded at run time (a model file, policy text) rather than code',
  'exceptions': 'control flow by throwing and catching',
  'external': 'state held outside the code read (a database query, Redis script atomicity, another service)',
  'chart-subset': 'a statechart construct chart / fromXState does not take: invoke, after, always, inline guards and actions, entry/exit actions writing the context, a parallel state below the root',
  'two-key-map': 'a map keyed by two values (a mapping of mappings, a link table), encoded as one key',
  'two-run': 'a law comparing two runs of a rule (stickiness as the params change), not two requests of one run',
  'batch': 'a batch of operations that succeed or fail together (linked events, a transaction rolled back), or one operation over every due record',
  'scope': 'not a language gap: a part of the code left out of the rule by choice (an option, an admin path, a setting fixed for a run, a value shape simplified)',
  'other': 'see detail',
} as const
export type Gap_ = keyof typeof GAPS

export type RealItem = {
  id: string // `<domain>/<repo short>/<what>`
  domain: Domain
  source: Source
  also?: Source[] // further files the rule reads from (a test that fixes the intent, a type the step reads)
  summary: string // what the code does, in a sentence or two
  expressible: 'full' | 'partial' | 'none' // 'full': every part of the step said as the code does it
  gaps: Gap[]
  laws: RealLaw[]
  // Laws a reviewer would ask about that the language could not state (each gap names them): counted as not proven.
  unstated?: {name: string, kind: LawKind, intent: Intent, why: string}[]
}

const search = (ms: number) => ({search: {ms}})
// An invariant, alone, with the default search.
export const invariant = (r: AnyRule, law: Law, kind: LawKind, intent: Intent, why: string): RealLaw =>
  ({name: law.name, kind, intent, why, form: 'invariant', prove: ms => proveRule(r, [law], search(ms))})
// A one-step (or k-step) law, alone: the search finds the invariants it assumes.
export const stepLaw = (r: AnyRule, sl: StepLaw, kind: LawKind, intent: Intent, why: string): RealLaw =>
  ({name: sl.name, kind, intent, why, form: 'step', prove: ms => proveSteps(r, [], [sl], search(ms))})
// "Whenever from, later to" under fairness, with no rank and no invariant given (the spec leaves `rank` out: the search finds both).
export const leadsTo = (r: AnyRule, l: Liveness, intent: Intent, why: string, kind: LawKind = 'liveness'): RealLaw => {
  if (!Array.isArray(l.rank) || l.rank.length) throw new Error(`${l.name}: a corpus liveness states no rank (leave rank out)`)
  return {name: l.name, kind, intent, why, form: 'leadsTo', live: {r, l}, prove: ms => proveLeadsTo(r, [], l, {ms})}
}
// A claim about one request (an access check, an entitlement).
export const decision = (d: AnyDecision, kind: LawKind, intent: Intent, why: string): RealLaw =>
  ({name: d.name, kind, intent, why, form: 'decision', prove: ms => proveDecision(d, {ms})})
// A chart's law or step law: with the chart's structural laws, which `chart.prove` adds itself.
export const chartLaw = (c: AnyChart, law: Law, kind: LawKind, intent: Intent, why: string): RealLaw =>
  ({name: law.name, kind, intent, why, form: 'invariant', prove: ms => proveRule(c.rule, [...c.chartLaws(), law], search(ms))})
export const chartStep = (c: AnyChart, sl: StepLaw, kind: LawKind, intent: Intent, why: string): RealLaw =>
  ({name: sl.name, kind, intent, why, form: 'step', prove: ms => proveSteps(c.rule, c.chartLaws(), [sl], search(ms))})
