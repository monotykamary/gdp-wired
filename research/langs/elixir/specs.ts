// Elixir packages' stateful modules, read by gdp-wired's Elixir front end (core/extract-ex.ts): what each item reads,
// and the laws, written against the extracted rule's names. `run.ts` fetches each package at its pinned version from
// hex.pm, extracts it (checked against the package's own module, compiled and run by core/ex/harness.exs), and proves
// the laws; research/realworld/items/elixir-hex.ts scores the rules extracted at the pins with the corpus.
import {type Cond, type StepLaw, all} from '../../../core/dsl.ts'
import type {Law} from '../../../core/machine.ts'
import type {ExOptions} from '../../../core/extract-ex.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type X = any
type R = {stepLaw: (name: string, then: (b: X, a: X) => Cond, when?: (b: X) => Cond) => StepLaw, law: (name: string, f: (s: X) => Cond) => Law}
export type ExLaw = {name: string, kind: 'step' | 'access' | 'safety', intent: 'docs' | 'tests' | 'inferred', why: string, law: (r: R) => StepLaw | Law}
export type ExSpec = {id: string, domain: 'circuit breaker' | 'rate limit', pkg: string, version: string, licence: string, author: string, repo: string,
  file: string, reads: string, summary: string, opts: Omit<ExOptions, 'elixir'>, laws: ExLaw[]}

export const SPECS: ExSpec[] = [
  {id: 'circuit breaker/ex_break/Breaker', domain: 'circuit breaker', pkg: 'ex_break', version: '0.0.9', licence: 'MIT', author: 'Jonathan Clem', repo: 'jclem/ex_break',
    file: 'lib/ex_break/breaker.ex', reads: 'lib/ex_break/breaker.ex: ExBreak.Breaker.increment, is_tripped, reset_tripped (an Agent over the breaker struct)',
    summary: 'A circuit breaker for one function, an Agent over a struct: each failure counted, the breaker tripped (and the time recorded) once the count reaches the threshold, read as tripped while the timeout since it tripped hasn\'t passed, reset to a new breaker.',
    opts: {entry: 'ExBreak.Breaker'},
    laws: [
      {name: 'a failure that reaches the threshold trips the breaker', kind: 'step', intent: 'docs', why: 'breaker.ex: "If the new break count exceeds the given threshold, the breaker is also marked as tripped"',
        law: r => r.stepLaw('a failure that reaches the threshold trips the breaker', (b, a) => a.tripped.iff(b.increment_threshold.atMost(b.break_count.plus(1))), b => b.method.is('increment'))},
      {name: 'a tripped breaker knows when it tripped', kind: 'safety', intent: 'inferred', why: 'increment sets tripped_at exactly where it sets tripped; is_tripped reads it where tripped holds',
        law: r => r.law('a tripped breaker knows when it tripped', s => s.tripped.implies(s.tripped_at_none.not()))},
      {name: 'a reset clears a tripped breaker', kind: 'step', intent: 'docs', why: 'breaker.ex: "Reset a tripped circuit breaker by creating a new circuit breaker"',
        law: r => r.stepLaw('a reset clears a tripped breaker', (_b, a) => all(a.break_count.eq(0), a.tripped.not(), a.tripped_at_none), b => all(b.method.is('reset_tripped'), b.tripped))},
      {name: 'a breaker not tripped is never read as tripped', kind: 'access', intent: 'docs', why: 'is_tripped: "if breaker.tripped do ... else false"',
        law: r => r.stepLaw('a breaker not tripped is never read as tripped', (_b, a) => a.is_tripped_result.not(), b => all(b.method.is('is_tripped'), b.tripped.not()))},
    ]},
]
// Read and refused, each where it leaves the subset (research/langs/DESIGN.md): odo 0.1.0's Odo.Bucket (get_token
// divides by a field, `div(diff, tick_duration)`; tick_started_at is :init or a number) and attempt 0.6.0's
// Attempt.Bucket.Token (its queue is an Erlang :queue, its refill a timer message, its errors another module's).
