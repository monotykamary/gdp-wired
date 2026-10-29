// Rust crates' stateful rules, read by gdp-wired's Rust front end (core/extract-rs.ts): what each item reads, and the
// laws, written against the extracted rule's names. `run.ts` fetches each crate at its pinned version from crates.io,
// extracts it (checked against the crate's own code, built with cargo), and proves the laws;
// research/realworld/items/rust-crates.ts scores the rules extracted at the pins with the corpus.
import {type Cond, type StepLaw, all} from '../../../core/dsl.ts'
import type {Law} from '../../../core/machine.ts'
import type {RsOptions} from '../../../core/extract-rs.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type X = any
type R = {stepLaw: (name: string, then: (b: X, a: X) => Cond, when?: (b: X) => Cond) => StepLaw, law: (name: string, f: (s: X) => Cond) => Law}
export type RsLaw = {name: string, kind: 'step' | 'access' | 'safety', intent: 'docs' | 'tests' | 'inferred', why: string, law: (r: R) => StepLaw | Law}
export type RsSpec = {id: string, domain: 'rate limit' | 'circuit breaker', crate: string, version: string, licence: string, author: string, repo: string,
  reads: string, summary: string, opts: Omit<RsOptions, 'cargo'>, laws: RsLaw[]}
const lt = (x: X, y: X): Cond => { try { return x.lt(y) } catch { return y.gt(x) } }
const atMost = (x: X, y: X): Cond => { try { return x.atMost(y) } catch { return y.atLeast(x) } }

export const SPECS: RsSpec[] = [
  {id: 'rate limit/gcra/GcraState', domain: 'rate limit', crate: 'gcra', version: '0.6.0', licence: 'MIT', author: 'Sam Shih', repo: 'lytefast/gcra-rs',
    reads: 'src/gcra.rs: GcraState::check_and_modify_at, revert_at (and the closures in them); src/rate_limit.rs: RateLimit::increment_interval',
    summary: 'The generic cell rate algorithm: a request of a cost is allowed while the theoretical arrival time, moved by the cost\'s emission interval, stays within one period of the arrival; an allowed request moves it, a revert takes it back.',
    opts: {entry: 'GcraState', methods: ['check_and_modify_at', 'revert_at'], failures: 'kept'},
    laws: [
      {name: 'an allowed request leaves the theoretical arrival time at most one period past its arrival', kind: 'safety', intent: 'docs', why: 'gcra.rs: "next_allowed_at <= arrived_at" with next_allowed_at = new_tat - period',
        law: r => r.stepLaw('an allowed request leaves the theoretical arrival time at most one period past its arrival', (b, a) => a.failed.not().implies(atMost(a.tat, b.check_and_modify_at_arrived_at.plus(b.check_and_modify_at_rate_limit_period))), b => b.method.is('check_and_modify_at'))},
      {name: 'a denied request changes nothing', kind: 'step', intent: 'docs', why: 'gcra.rs: Err(DeniedUntil) / Err(DeniedIndefinitely) return before self.tat is set',
        law: r => r.stepLaw('a denied request changes nothing', (b, a) => a.failed.implies(all(a.tat.eq(b.tat), a.tat_none.iff(b.tat_none))), b => b.method.is('check_and_modify_at'))},
      {name: 'an allowed request never moves the theoretical arrival time back', kind: 'step', intent: 'inferred', why: 'GCRA: tat\' = max(tat, arrival) + interval',
        law: r => r.stepLaw('an allowed request never moves the theoretical arrival time back', (b, a) => a.failed.not().implies(atMost(b.tat, a.tat)), b => b.method.is('check_and_modify_at').and(b.tat_none.not()))},
      {name: 'a request whose cost takes longer than the period is denied', kind: 'access', intent: 'docs', why: 'gcra.rs: "if increment_interval > rate_limit.period { return Err(GcraError::DeniedIndefinitely ..."',
        law: r => r.stepLaw('a request whose cost takes longer than the period is denied', (_b, a) => a.failed, b => all(b.method.is('check_and_modify_at'), lt(b.check_and_modify_at_rate_limit_period, b.check_and_modify_at_rate_limit_emission_interval.mul(b.check_and_modify_at_cost))))},
      {name: 'a revert never moves the theoretical arrival time later', kind: 'step', intent: 'inferred', why: 'revert_at: tat - increment_interval, or None once it has passed',
        law: r => r.stepLaw('a revert never moves the theoretical arrival time later', (b, a) => all(a.failed.not(), a.tat_none.not()).implies(atMost(a.tat, b.tat)), b => all(b.method.is('revert_at'), b.tat_none.not()))},
    ]},
  {id: 'circuit breaker/circuitbreaker-rs/StateManager', domain: 'circuit breaker', crate: 'circuitbreaker-rs', version: '0.1.1', licence: 'MIT OR Apache-2.0', author: 'circuitbreaker-rs authors', repo: 'crates.io/crates/circuitbreaker-rs',
    reads: 'src/state.rs: StateManager::new, current, transition_from_to, trip_open, attempt_half_open, reset_closed, revert_to_open; State::from',
    summary: 'A circuit breaker\'s state in an AtomicU8 (Closed 0, Open 1, HalfOpen 2) moved by compare-and-swap transitions, each successful one recording its time under a Mutex.',
    opts: {entry: 'StateManager', methods: ['trip_open', 'attempt_half_open', 'reset_closed', 'revert_to_open', 'current'], failures: 'kept'},
    laws: [
      {name: 'the state is always Closed, Open or HalfOpen', kind: 'safety', intent: 'docs', why: 'state.rs: "enum State { Closed = 0, Open = 1, HalfOpen = 2 }"', law: r => r.law('the state is always Closed, Open or HalfOpen', ({state}) => state.atMost(2))},
      {name: 'a breaker goes half-open only from open', kind: 'step', intent: 'docs', why: 'attempt_half_open: transition_from_to(State::Open, State::HalfOpen)',
        law: r => r.stepLaw('a breaker goes half-open only from open', (b, a) => a.attempt_half_open_result.implies(all(b.state.eq(1), a.state.eq(2))), b => b.method.is('attempt_half_open'))},
      {name: 'trip_open opens a breaker that is not open', kind: 'step', intent: 'docs', why: 'trip_open: "if current == State::Open { return false }" then transition_from_to(current, State::Open)',
        law: r => r.stepLaw('trip_open opens a breaker that is not open', (_b, a) => all(a.state.eq(1), a.trip_open_result), b => all(b.method.is('trip_open'), b.state.eq(1).not()))},
      {name: 'a transition taken records its time', kind: 'step', intent: 'docs', why: 'transition_from_to: "if result { *self.last_transition.lock() = Instant::now() }"',
        law: r => r.stepLaw('a transition taken records its time', (b, a) => a.reset_closed_result.implies(a.last_transition.eq(b.now)), b => b.method.is('reset_closed'))},
      {name: 'a transition refused changes nothing', kind: 'step', intent: 'docs', why: 'transition_from_to: compare_exchange fails, nothing written',
        law: r => r.stepLaw('a transition refused changes nothing', (b, a) => a.revert_to_open_result.not().implies(all(a.state.eq(b.state), a.last_transition.eq(b.last_transition))), b => b.method.is('revert_to_open'))},
    ]},
]
