// Electric (electric-sql/electric), the agents runtime's pull-wake runner lifecycle, XState v5. Apache-2.0, (c)
// ElectricSQL. https://github.com/electric-sql/electric/blob/3f9809fb0bd894cb74470d434749673492ad7acf/packages/agents-runtime/src/pull-wake-machine.ts
//
// A long-lived wake stream: START connects; a connected stream is consumed until it ends or is reset, then the runner
// waits a backoff (doubling, capped at 30 s, reset to 1 s on a successful connect) and connects again; STOP drains and
// returns to stopped.
//
// fromXState refuses the machine (repro/xstate-refusals.ts): its first refusal is `invoke` on running.connecting; it
// also uses `after` (reconnecting), inline `assign` actions and inline guards, entry and exit actions that write the
// context (connecting's entry clears streamResetError, streaming's exit clears response) and a callback actor. So the
// chart is written by hand, one transition per transition of the code (line numbers cite the file above):
//   - the invoked connectStream promise's onDone / onError are the events CONNECT_DONE / CONNECT_ERROR, sent only
//     while connecting (leaving connecting cancels it, :135-136); shutdown's are SHUTDOWN_DONE / SHUTDOWN_ERROR;
//   - the `after: {reconnectBackoff}` timer firing is the event RETRY, only while reconnecting (leaving cancels it);
//   - consumeStream's sendBack (WAKE, OFFSET, STREAM_END) are events while streaming; STREAM_END's `error` is the
//     payload `failed`;
//   - the context's objects as what the code reads of them: `response` non-null as hasResponse, streamResetError and
//     drainError non-null as resetError and drained. The effects (heartbeats, cancelResponse, onWake ...) aren't
//     state.
import {bool, min, no, yes, when} from '../../../core/dsl.ts'
import {chart} from '../../../core/chart.ts'
import {type RealItem, chartLaw, chartStep, leadsTo} from '../lib.ts'

const src = {repo: 'electric-sql/electric', commit: '3f9809fb0bd894cb74470d434749673492ad7acf', licence: 'Apache-2.0', author: 'ElectricSQL', language: 'TypeScript'}

const INITIAL = 1000, MAX = 30000 // :4-5 INITIAL_RECONNECT_BACKOFF_MS, MAX_RECONNECT_BACKOFF_MS
export const events = ['START', 'STOP', 'CONNECT_DONE', 'CONNECT_ERROR', 'STREAM_RESET', 'WAKE', 'OFFSET', 'STREAM_END', 'RETRY', 'SHUTDOWN_DONE', 'SHUTDOWN_ERROR'] as const
export const pullWake = () => chart('pullWakeRunner')
  .events(...events)
  .inputs({failed: bool}) // STREAM_END's `error` (:181-191)
  // :88-93
  .context({backoffMs: INITIAL, hasResponse: {kind: bool, init: false}, resetError: {kind: bool, init: false}, drained: {kind: bool, init: false}})
  // :94-220
  .states({
    stopped: {},
    running: {states: {connecting: {}, streaming: {}, reconnecting: {}}},
    stopping: {},
  })
  // :97-107 START: running (its initial, connecting: whose entry clears streamResetError, :116-118), the context reset
  .on('START', {from: 'stopped', to: 'running', set: () => ({backoffMs: INITIAL, hasResponse: no, resetError: no, drained: no})})
  // :111-113 STOP from anywhere in running; streaming's exit (:145-157) clears the response
  .on('STOP', {from: 'running', to: 'stopping', set: env => ({hasResponse: when(env.in('running.streaming'), no, env.hasResponse)})})
  // :120-128 connectStream's onDone: the response kept, the backoff reset
  .on('CONNECT_DONE', {from: 'running.connecting', to: 'running.streaming', set: () => ({hasResponse: yes, backoffMs: INITIAL})})
  // :129-132 onError
  .on('CONNECT_ERROR', {from: 'running.connecting', to: 'running.reconnecting'})
  // :137-140 a reset while connecting aborts the attempt
  .on('STREAM_RESET', {from: 'running.connecting', to: 'running.reconnecting'})
  // :163-166 effects only
  .on('WAKE', {from: 'running.streaming'})
  .on('OFFSET', {from: 'running.streaming'})
  // :167-180 guard `!context.streamResetError`: the error recorded, the stream cancelled
  .on('STREAM_RESET', {from: 'running.streaming', when: ({resetError}) => resetError.not(), set: () => ({resetError: yes})})
  // :181-192 both branches go to reconnecting (the first also reports the error); streaming's exit clears the response
  .on('STREAM_END', {from: 'running.streaming', to: 'running.reconnecting', set: () => ({hasResponse: no})})
  // :197-205 the reconnectBackoff timer: back to connecting (its entry clears streamResetError), the backoff doubled
  .on('RETRY', {from: 'running.reconnecting', to: 'running.connecting', set: ({backoffMs}) => ({backoffMs: min(backoffMs.times(2), MAX), resetError: no})})
  // :211-218 shutdown's onDone / onError (the error kept)
  .on('SHUTDOWN_DONE', {from: 'stopping', to: 'stopped'})
  .on('SHUTDOWN_ERROR', {from: 'stopping', to: 'stopped', set: () => ({drained: yes})})

const c = pullWake()
const ev = (e: (typeof events)[number]) => events.indexOf(e)
export const items: RealItem[] = [{
  id: 'xstate/electric/pullWakeRunner',
  domain: 'xstate',
  source: {...src, path: 'packages/agents-runtime/src/pull-wake-machine.ts', lines: '45-222', export: 'createPullWakeMachine'},
  summary: 'A wake-stream runner: connect, consume the stream, on an end or reset wait a doubling backoff (1 s to 30 s, reset on connect) and reconnect; STOP drains back to stopped.',
  expressible: 'partial',
  gaps: [
    {gap: 'async', blocks: 'part', detail: 'invoke (connectStream and shutdown promises, the consumeStream callback actor) and `after: {reconnectBackoff}`: their completions and the timer are events sent from outside (CONNECT_DONE/ERROR, SHUTDOWN_DONE/ERROR, RETRY, WAKE/OFFSET/STREAM_END), each only in the state that owns it; the delay\'s length (backoffMs) is not time the chart waits'},
    {gap: 'other', blocks: 'part', detail: 'fromXState refuses it: invoke on running.connecting (first), and also after, inline assign actions and guards, entry/exit actions that write the context; the chart is by hand, the entry and exit writes folded into the transitions that enter connecting or leave streaming'},
    {gap: 'other', blocks: 'part', detail: 'context objects (response, streamResetError, drainError) as whether they are set'},
  ],
  laws: [
    chartLaw(c, c.law('the backoff stays between 1 s and 30 s', ({backoffMs}) => backoffMs.atLeast(INITIAL).and(backoffMs.atMost(MAX))),
      'safety', 'docs', ':4-5 INITIAL_RECONNECT_BACKOFF_MS = 1_000, MAX_RECONNECT_BACKOFF_MS = 30_000; :202 Math.min(context.backoffMs * 2, MAX_RECONNECT_BACKOFF_MS)'),
    chartLaw(c, c.law('a stream response is held only while streaming', env => env.hasResponse.implies(env.in('running.streaming'))),
      'safety', 'docs', ':147-151 streaming\'s exit cancels the response ("pull wake runner stopped") and clears it'),
    chartStep(c, c.stepLaw('STOP while running always goes to stopping', (_, after) => after.in('stopping'), b => b.in('running').and(b.event.is('STOP'))),
      'step', 'docs', ':8-10 "the machine decides *when* they happen so every (state, event) pair is explicit"; :111-113 STOP on running'),
    chartStep(c, c.stepLaw('a successful connect resets the backoff', (_, after) => after.backoffMs.eq(INITIAL), b => b.in('running.connecting').and(b.event.is('CONNECT_DONE'))),
      'step', 'inferred', ':124-127 onDone assigns backoffMs: INITIAL_RECONNECT_BACKOFF_MS'),
    chartStep(c, c.stepLaw('a second reset while streaming changes nothing', (b, after) => after.in('running.streaming').and(after.resetError, after.backoffMs.eq(b.backoffMs)), b => b.in('running.streaming').and(b.resetError, b.event.is('STREAM_RESET'))),
      'step', 'docs', ':168 guard `!context.streamResetError`; :169-172 "Cancel the stream; the consume actor then observes the end"'),
    chartStep(c, c.stepLaw('START while not stopped changes nothing', (b, after) => after.backoffMs.eq(b.backoffMs).and(after.in('stopped').not()), b => b.in('stopped').not().and(b.event.is('START'))),
      'step', 'inferred', 'START is handled only in stopped (:97-107): an event the other states do not accept'),
    leadsTo(c.rule, c.rule.leadsTo('a started runner always comes back to stopped', {
      // waiting: running or draining (a liveness's `from` holds until `to`)
      from: env => c.in(env, 'running').or(c.in(env, 'stopping')),
      to: env => c.in(env, 'stopped'),
      helpful: [{when: env => c.in(env, 'running'), request: () => ({event: ev('STOP')})}, {when: env => c.in(env, 'stopping'), request: () => ({event: ev('SHUTDOWN_DONE')})}],
    }), 'docs', ':24 "Drain sequence: wait for claim actors, abort wakes, drain wakes." then stopped (:213-217): STOP, then shutdown settling, ends in stopped'),
  ],
}]
