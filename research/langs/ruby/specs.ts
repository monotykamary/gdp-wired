// Ruby gems' stateful classes, read by gdp-wired's Ruby front end (core/extract-rb.ts): what each item reads, and the
// laws, written against the extracted rule's names. `run.ts` fetches each gem at its pinned version from rubygems.org,
// extracts it (checked against the gem's own code, run by core/rb/harness.rb), and proves the laws;
// research/realworld/items/ruby-gems.ts scores the rules extracted at the pins with the corpus.
import {type Cond, type StepLaw, all, any} from '../../../core/dsl.ts'
import type {Law} from '../../../core/machine.ts'
import type {RbOptions} from '../../../core/extract-rb.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type X = any
type R = {stepLaw: (name: string, then: (b: X, a: X) => Cond, when?: (b: X) => Cond) => StepLaw, law: (name: string, f: (s: X) => Cond) => Law}
export type RbLaw = {name: string, kind: 'step' | 'access' | 'safety', intent: 'docs' | 'tests' | 'inferred', why: string, law: (r: R) => StepLaw | Law}
export type RbSpec = {id: string, domain: 'circuit breaker', gem: string, version: string, licence: string, author: string, repo: string,
  file: string, reads: string, summary: string, opts: Omit<RbOptions, 'ruby' | 'root'>, laws: RbLaw[]}

export const SPECS: RbSpec[] = [
  {id: 'circuit breaker/semian/Simple::State', domain: 'circuit breaker', gem: 'semian', version: '0.28.4', licence: 'MIT', author: 'Shopify', repo: 'Shopify/semian',
    file: 'lib/semian/simple_state.rb', reads: 'lib/semian/simple_state.rb: Semian::Simple::State#open!, close!, half_open!, reset, open?, closed?, half_open?',
    summary: 'The state of Semian\'s circuit breaker (the single-process one): closed, open or half open, moved by open!, close! and half_open!, reset closing it, read by its predicates.',
    opts: {entry: 'Semian::Simple::State', methods: ['open!', 'close!', 'half_open!', 'reset', 'open?', 'closed?', 'half_open?']},
    laws: [
      {name: 'open! opens the breaker', kind: 'step', intent: 'docs', why: 'simple_state.rb: "def open!; @value = :open; end"', law: r => r.stepLaw('open! opens the breaker', (_b, a) => a.value.is('open'), b => b.method.is('open!'))},
      {name: 'reset closes the breaker', kind: 'step', intent: 'docs', why: 'simple_state.rb: "def reset; close!; end"', law: r => r.stepLaw('reset closes the breaker', (_b, a) => a.value.is('closed'), b => b.method.is('reset'))},
      {name: 'open? is whether the breaker is open', kind: 'step', intent: 'docs', why: 'simple_state.rb: "def open?; value == :open; end"', law: r => r.stepLaw('open? is whether the breaker is open', (b, a) => a.open_p_result.iff(b.value.is('open')), b => b.method.is('open?'))},
      {name: 'a predicate changes nothing', kind: 'step', intent: 'inferred', why: 'open?, closed? and half_open? only read @value',
        law: r => r.stepLaw('a predicate changes nothing', (b, a) => a.value.eq(b.value), b => any(b.method.is('open?'), b.method.is('closed?'), b.method.is('half_open?')))},
    ]},
  {id: 'circuit breaker/semian/Simple::Integer', domain: 'circuit breaker', gem: 'semian', version: '0.28.4', licence: 'MIT', author: 'Shopify', repo: 'Shopify/semian',
    file: 'lib/semian/simple_integer.rb', reads: 'lib/semian/simple_integer.rb: Semian::Simple::Integer#increment, reset',
    summary: 'The success counter of Semian\'s circuit breaker (a half-open breaker closes once it reaches the success threshold): increment by a value (1 by default), reset to 0.',
    opts: {entry: 'Semian::Simple::Integer', methods: ['increment', 'reset']},
    laws: [
      {name: 'increment adds its value', kind: 'step', intent: 'docs', why: 'simple_integer.rb: "def increment(val = 1); @value += val; end"', law: r => r.stepLaw('increment adds its value', (b, a) => a.value.eq(b.value.plus(b.increment_val)), b => b.method.is('increment'))},
      {name: 'increment returns the new count', kind: 'step', intent: 'inferred', why: '@value += val is the method\'s last expression', law: r => r.stepLaw('increment returns the new count', (_b, a) => a.increment_result.eq(a.value), b => b.method.is('increment'))},
      {name: 'reset sets the count to 0', kind: 'step', intent: 'docs', why: 'simple_integer.rb: "def reset; @value = 0; end"', law: r => r.stepLaw('reset sets the count to 0', (_b, a) => a.value.eq(0), b => b.method.is('reset'))},
    ]},
  {id: 'circuit breaker/stoplight/Memory::Storage::State', domain: 'circuit breaker', gem: 'stoplight', version: '6.0.0', licence: 'MIT', author: 'Cameron Desautels, Taylor Fausak, Tëma Bolshakov',
    repo: 'bolshakov/stoplight', file: 'lib/stoplight/infrastructure/memory/storage/state.rb',
    reads: 'lib/stoplight/infrastructure/memory/storage/state.rb: Stoplight::Infrastructure::Memory::Storage::State#transition_to_color, clear (and transition_to_green, _yellow, _red)',
    summary: 'A light\'s state in memory: a transition to green, yellow or red under a mutex records when it was recovered, when recovery started, when it was breached and when recovery is next tried (red: the clock\'s time plus the cool-off), reporting whether the transition was new; clear unlocks it and forgets every time.',
    opts: {entry: 'Stoplight::Infrastructure::Memory::Storage::State', methods: ['transition_to_color', 'clear'], clocks: ['clock']},
    laws: [
      {name: 'red schedules the recovery one cool-off after now', kind: 'step', intent: 'docs', why: 'state.rb: "self.recovery_scheduled_after = current_time + cool_off_time"',
        law: r => r.stepLaw('red schedules the recovery one cool-off after now', (b, a) => all(a.recovery_scheduled_after_none.not(), b.cool_off_time_.plus(b.now).eq(a.recovery_scheduled_after)), b => all(b.method.is('transition_to_color'), b.transition_to_color_color.is('red')))},
      {name: 'a breach is recorded once, at the first red', kind: 'step', intent: 'docs', why: 'transition_to_red: "if breached_at then false else self.breached_at = current_time; true"',
        law: r => r.stepLaw('a breach is recorded once, at the first red', (b, a) => all(a.breached_at_none.not(), a.transition_to_color_result.iff(b.breached_at_none), b.breached_at_none.not().implies(a.breached_at.eq(b.breached_at))), b => all(b.method.is('transition_to_color'), b.transition_to_color_color.is('red')))},
      {name: 'a recovered light is never breached', kind: 'safety', intent: 'inferred', why: 'green sets recovered_at and clears breached_at; red and yellow clear recovered_at',
        law: r => r.law('a recovered light is never breached', s => any(s.recovered_at_none, s.breached_at_none))},
      {name: 'clear unlocks the light and forgets every time', kind: 'step', intent: 'docs', why: 'state.rb: clear sets locked_state UNLOCKED and recovered_at, recovery_scheduled_after, breached_at, recovery_started_at nil',
        law: r => r.stepLaw('clear unlocks the light and forgets every time', (_b, a) => all(a.locked_state.is('unlocked'), a.recovered_at_none, a.recovery_scheduled_after_none, a.breached_at_none, a.recovery_started_at_none), b => b.method.is('clear'))},
    ]},
]
