// Open Decision (open-decision/open-decision), the builder's Yjs sync websocket machine, XState v4 (4.34.0 in its
// yarn.lock). MIT, (c) 2021 Open Legal Tech e.V.
// https://github.com/open-decision/open-decision/blob/832e4c9f9f33778222c1c3153aad4060dbc9a26e/packages/tree/sync/src/websocket.machine.ts
// (the machine) and packages/tree/sync/src/treeStore/TreeContext.tsx:21-44 (what sends it events).
//
// OPEN authenticates (a token from the API), then opens the y-websocket provider; a connection error retries
// (after min(retries · 1 s, 20 s)) while under the retry limit of 10, then gives up in `error` (final, and
// TreeContext throws). CLOSE, RECONNECT, RETRY and connection.ready are events of the machine's type that no state
// handles.
//
// fromXState refuses the machine (repro/xstate-refusals.ts): `after` on retry first; it also uses `invoke` (a promise
// and a callback actor), and the v4 `cond` (which fromXState does not read at all: see the report). The chart is by
// hand, one transition per transition of the code:
//   - the authenticate promise's onDone / onError are AUTH_DONE / AUTH_ERROR, only while authenticating;
//   - the `after: {retry_delay}` timer firing is RETRY_DELAY, only in retry (its length is not modelled);
//   - the openWebsocket callback's `connection.ready` / `connection.error` are events from outside;
//   - id, yDoc, onSync and token (objects and strings) as whether they are set.
import {bool, yes} from '../../../core/dsl.ts'
import {chart} from '../../../core/chart.ts'
import {type RealItem, chartLaw, chartStep, leadsTo} from '../lib.ts'

const src = {repo: 'open-decision/open-decision', commit: '832e4c9f9f33778222c1c3153aad4060dbc9a26e', licence: 'MIT', author: 'Open Legal Tech e.V.', language: 'TypeScript'}

export const events = ['OPEN', 'CLOSE', 'RECONNECT', 'RETRY', 'connection.ready', 'connection.error', 'AUTH_DONE', 'AUTH_ERROR', 'RETRY_DELAY'] as const
export const websocket = () => chart('websocketMachine')
  .events(...events)
  // :47-53 (retryLimit: 10)
  .context({retryLimit: 10, retries: 0, hasDoc: {kind: bool, init: false}, hasToken: {kind: bool, init: false}})
  .states({unconnected: {}, retry: {}, authenticating: {}, connected: {}, error: {final: true}})
  // :55-59 OPEN → authenticating, assignDataToContext (:139-144: id, onSync, yDoc)
  .on('OPEN', {from: 'unconnected', to: 'authenticating', set: () => ({hasDoc: yes})})
  // :60-67 after retry_delay → authenticating, incrementRetries (:150)
  .on('RETRY_DELAY', {from: 'retry', to: 'authenticating', set: ({retries}) => ({retries: retries.plus(1)})})
  // :68-75 authenticate: onDone → connected, assignTokenToContext (:145-147); onError → error
  .on('AUTH_DONE', {from: 'authenticating', to: 'connected', set: () => ({hasToken: yes})})
  .on('AUTH_ERROR', {from: 'authenticating', to: 'error'})
  // :81-90 connection.error: [{cond underRetryLimit (:153-154 retries < retryLimit), target retry}, {target error}]
  .on('connection.error', {from: 'connected', to: 'retry', when: ({retries, retryLimit}) => retries.lt(retryLimit)})
  .on('connection.error', {from: 'connected', to: 'error'})

const c = websocket()
const ev = (e: (typeof events)[number]) => events.indexOf(e)
export const items: RealItem[] = [{
  id: 'xstate/open-decision/websocket',
  domain: 'xstate',
  source: {...src, path: 'packages/tree/sync/src/websocket.machine.ts', lines: '29-160', export: 'websocketMachine'},
  also: [{...src, path: 'packages/tree/sync/src/treeStore/TreeContext.tsx', lines: '21-44', export: 'TreeProvider'}],
  summary: 'The builder\'s sync connection: authenticate, open the Yjs websocket, retry a dropped connection after a growing delay up to 10 times, then fail for good.',
  expressible: 'partial',
  gaps: [
    {gap: 'async', blocks: 'part', detail: 'invoke (the authenticate promise, the openWebsocket callback actor with its own 5 s setTimeout) and `after: {retry_delay}`: their completions and the timer are events from outside; the delay min(retries * 1000, 20000) is not time the chart waits'},
    {gap: 'other', blocks: 'part', detail: 'fromXState refuses it: `after` on retry (first), and `invoke`; its v4 guard `cond: "underRetryLimit"` is not read by fromXState at all (it reads v5 `guard` only: a v4 cond is dropped without a refusal); the chart is by hand'},
    {gap: 'other', blocks: 'part', detail: 'id, yDoc, onSync and token (objects and strings) as whether they are set'},
  ],
  laws: [
    chartLaw(c, c.law('the retries stay within the retry limit', ({retries, retryLimit}) => retries.atMost(retryLimit)),
      'safety', 'inferred', ':50 retryLimit: 10; :153-154 underRetryLimit: retries < retryLimit'),
    chartStep(c, c.stepLaw('error is never left', (_, after) => after.in('error'), b => b.in('error')),
      'step', 'docs', ':92-94 error: {type: "final"}; TreeContext.tsx:23-28 throws WEBSOCKET_CONNECTION_FAILED there'),
    chartStep(c, c.stepLaw('a dropped connection under the limit is retried', (_, after) => after.in('retry'), b => b.in('connected').and(b.event.is('connection.error'), b.retries.lt(b.retryLimit))),
      'step', 'inferred', ':82-88 connection.error under underRetryLimit → retry'),
    chartStep(c, c.stepLaw('OPEN while connected changes nothing', (b, after) => after.in('connected').and(after.retries.eq(b.retries)), b => b.in('connected').and(b.event.is('OPEN'))),
      'step', 'inferred', 'OPEN is handled only in unconnected (:55-59)'),
    // Refuted (repro/open-decision-websocket.ts): no state handles CLOSE, so the open websocket stays open (the
    // invoked callback's cleanup, websocket.destroy(), runs only when connected is left). A suspected real bug
    // (triage/xstate.json): TreeContext.tsx:40-42 sends CLOSE when its effect is cleaned up (the tree id changes).
    chartStep(c, c.stepLaw('CLOSE ends an open connection', (_, after) => after.in('connected').not(), b => b.in('connected').and(b.event.is('CLOSE'))),
      'step', 'docs', 'TreeContext.tsx:40-42 the effect\'s cleanup `send({ type: "CLOSE" })`; :23 Events includes { type: "CLOSE" }'),
    // Refuted (same repro): connection.ready is never handled, so retries only grow: ten drops over a session's life,
    // each followed by a good reconnect, end the session in error. A suspected real bug (triage/xstate.json).
    chartStep(c, c.stepLaw('a synced connection resets the retries', (_, after) => after.retries.eq(0), b => b.in('connected').and(b.event.is('connection.ready'))),
      'step', 'inferred', ':119-122 the provider sends connection.ready on sync; a retry limit of 10 counts consecutive failures (the delay grows with retries, :157)'),
    leadsTo(c.rule, c.rule.leadsTo('an opening connection ends connected or failed', {
      from: env => c.in(env, 'retry').or(c.in(env, 'authenticating')),
      to: env => c.in(env, 'connected').or(c.in(env, 'error')),
      helpful: [{when: env => c.in(env, 'retry'), request: () => ({event: ev('RETRY_DELAY')})}, {when: env => c.in(env, 'authenticating'), request: () => ({event: ev('AUTH_DONE')})}],
    }), 'inferred', 'authenticating settles (onDone/onError, :71-73) and the retry timer fires (:61-66)'),
  ],
}]
