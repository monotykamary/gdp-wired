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
