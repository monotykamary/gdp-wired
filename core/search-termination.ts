// Diagnostic provenance, never proof authority. Capture the cause at its clock/budget
// boundary before unwinding; elapsed duration and reason strings are not evidence.
export type SearchTermination = {
  kind: 'wall-deadline' | 'work-exhausted'
  phase: string
  scope?: 'search' | 'stage'
}
export type SearchContext = {
  goal?: string
  stuck?: string
  why?: string
  witness?: Record<string, number>
}
export type SearchTerminationFields = {
  stopped?: true
  termination?: SearchTermination
  context?: SearchContext
}
export const searchContext = (v: SearchContext & SearchTerminationFields): SearchContext => v.context ?? ({
  ...(v.goal === undefined ? {} : {goal: v.goal}), ...(v.stuck === undefined ? {} : {stuck: v.stuck}),
  ...(v.why === undefined ? {} : {why: v.why}), ...(v.witness === undefined ? {} : {witness: v.witness}),
})
export const terminationWhy = (t: SearchTermination): string =>
  `${t.kind === 'wall-deadline' ? 'wall deadline reached' : 'counted work exhausted'} (${t.phase}${t.scope === 'stage' ? '; stage allowance' : ''})`
type Completion = {
  proven: boolean, checked: boolean, run?: unknown, fairRing?: unknown, kernelProven?: boolean, translation?: string,
  stopped?: boolean, termination?: unknown, stats?: {stopped?: boolean, termination?: unknown},
}
// Terminal evidence of source refusal, never permission to publish a proof.
// In particular, neither a generic unknown nor interrupted source checking is
// completed merely because its mathematical part once succeeded.
export const completedSourceRefusal = (v: Completion | undefined): boolean =>
  !!v && v.proven === false && v.checked === false && v.kernelProven === true &&
  (v.translation === 'unchecked' || v.translation === 'error') &&
  v.stopped === undefined && v.termination === undefined && !v.stats?.stopped && v.stats?.termination === undefined
export const completedSearch = (v: Completion | undefined): boolean =>
  !!v && (v.proven && v.checked || v.run !== undefined || !!v.fairRing || completedSourceRefusal(v))
export const stoppedSearch = <T extends SearchContext & SearchTerminationFields>(v: T, termination: SearchTermination): T & SearchTerminationFields =>
  ({...v, stopped: true, termination, context: searchContext(v), why: terminationWhy(termination)})
