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
  | 'state machine' // debounces, link and connection states
  | 'distributed' // consensus logs and votes, leases, dedupe, idempotency keys, clocks

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
// Keep the original corpus pair available for independent replay and for
// joint-proof fallback on the same rule/prelude without altering corpus items.
export type JointSpec =
  | {rule: AnyRule, prelude: Law[], kind: 'invariant', law: Law}
  | {rule: AnyRule, prelude: Law[], kind: 'step', step: StepLaw}
const invariantInputs = new WeakMap<RealLaw, readonly [AnyRule, Law]>()
const jointSpecs = new WeakMap<RealLaw, JointSpec>()
const decisionInputs = new WeakMap<RealLaw, AnyDecision>()
export const invariantInput = (row: RealLaw) => invariantInputs.get(row)
export const jointSpec = (row: RealLaw): JointSpec | undefined => jointSpecs.get(row)
export const decisionInput = (row: RealLaw): AnyDecision | undefined => decisionInputs.get(row)
// An invariant, alone, with the default search.
export const invariant = (r: AnyRule, law: Law, kind: LawKind, intent: Intent, why: string): RealLaw => {
  const row: RealLaw = {name: law.name, kind, intent, why, form: 'invariant', prove: ms => proveRule(r, [law], search(ms))}
  invariantInputs.set(row, [r, law])
  jointSpecs.set(row, {rule: r, prelude: [], kind: 'invariant', law})
  return row
}
// A one-step (or k-step) law, alone: the search finds the invariants it assumes.
export const stepLaw = (r: AnyRule, sl: StepLaw, kind: LawKind, intent: Intent, why: string): RealLaw => {
  const row: RealLaw = {name: sl.name, kind, intent, why, form: 'step', prove: ms => proveSteps(r, [], [sl], search(ms))}
  jointSpecs.set(row, {rule: r, prelude: [], kind: 'step', step: sl})
  return row
}
// "Whenever from, later to" under fairness, with no rank and no invariant given (the spec leaves `rank` out: the search finds both).
export const leadsTo = (r: AnyRule, l: Liveness, intent: Intent, why: string, kind: LawKind = 'liveness'): RealLaw => {
  if (!Array.isArray(l.rank) || l.rank.length) throw new Error(`${l.name}: a corpus liveness states no rank (leave rank out)`)
  return {name: l.name, kind, intent, why, form: 'leadsTo', live: {r, l}, prove: ms => proveLeadsTo(r, [], l, {ms})}
}
// A claim about one request (an access check, an entitlement).
export const decision = (d: AnyDecision, kind: LawKind, intent: Intent, why: string): RealLaw => {
  const row: RealLaw = {name: d.name, kind, intent, why, form: 'decision', prove: ms => proveDecision(d, {ms})}
  decisionInputs.set(row, d)
  return row
}
// A chart's law or step law: with the chart's structural laws, which `chart.prove` adds itself.
export const chartLaw = (c: AnyChart, law: Law, kind: LawKind, intent: Intent, why: string): RealLaw => {
  const prelude = c.chartLaws()
  const row: RealLaw = {name: law.name, kind, intent, why, form: 'invariant', prove: ms => proveRule(c.rule, [...c.chartLaws(), law], search(ms))}
  jointSpecs.set(row, {rule: c.rule, prelude, kind: 'invariant', law})
  return row
}
export const chartStep = (c: AnyChart, sl: StepLaw, kind: LawKind, intent: Intent, why: string): RealLaw => {
  const prelude = c.chartLaws()
  const row: RealLaw = {name: sl.name, kind, intent, why, form: 'step', prove: ms => proveSteps(c.rule, c.chartLaws(), [sl], search(ms))}
  jointSpecs.set(row, {rule: c.rule, prelude, kind: 'step', step: sl})
  return row
}

// Prove one corpus law. Only when its ordinary proof ends unknown (neither proven nor refuted), retry it jointly with
// the other laws stated on the same rule and prelude within the time left in this law's own budget. Credit only law k,
// and only if the kernel checks the whole joint family (law k included). Never change a proven or refuted verdict.
export function proveItemLaw(it: RealItem, k: number, ms: number): Verdict {
  const l = it.laws[k]
  if (!l) throw new Error(`${it.id} has no law ${k}`)
  const t0 = performance.now()
  const v = l.prove(ms)
  const decided = (v.proven && v.checked) || v.proven || !!v.run || !!v.fairRing || !!v.acceleratedRun?.checked
    || (l.form === 'decision' && v.stuck === 'sat' && !!v.witness)
  if (decided || (v.stopped && v.termination?.kind === 'wall-deadline') || v.translation === 'unchecked' || v.translation === 'error') return v
  const target = jointSpecs.get(l)
  if (!target) return v
  const remaining = Math.floor(ms - (performance.now() - t0))
  if (remaining < 1) return v
  const preludeKey = JSON.stringify(target.prelude)
  const group: JointSpec[] = []
  let targetIncluded = false
  for (const sibling of it.laws) {
    const spec = jointSpecs.get(sibling)
    if (!spec || spec.rule !== target.rule || JSON.stringify(spec.prelude) !== preludeKey) continue
    if (sibling === l) targetIncluded = true
    group.push(spec)
  }
  if (!targetIncluded || group.length < 2) return v
  const invariants = [...target.prelude, ...group.filter((g): g is Extract<JointSpec, {kind: 'invariant'}> => g.kind === 'invariant').map(g => g.law)]
  const steps = group.filter((g): g is Extract<JointSpec, {kind: 'step'}> => g.kind === 'step').map(g => g.step)
  let jv: Verdict
  try {
    const opts = {search: {ms: remaining}, watchdogMs: remaining}
    jv = steps.length ? proveSteps(target.rule, invariants, steps, opts) : proveRule(target.rule, invariants, opts)
  } catch { return v }
  return jv.proven && jv.checked && jv.translation !== 'unchecked' && jv.translation !== 'error' ? jv : v
}
