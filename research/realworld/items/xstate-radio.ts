// radio-room (albatrocity), the web app's radio stream listener lifecycle, XState v5. MIT (the repo's LICENSE).
// https://github.com/albatrocity/radio-room/blob/cefbd86daa0c6eefcfb1ac02b7a725eb2be16ac4/apps/web/src/machines/radioStreamMachine.ts
//
// PLAY with a url connects (`active`: loading until the element plays); when the element ends or errors the machine
// waits 1.2 s and reconnects, up to 3 consecutive failures without reaching playback, then `failed`; PAUSE and
// TEARDOWN return to idle; SET_URL while playing switches streams.
//
// fromXState refuses the machine (repro/xstate-refusals.ts): `always` on idle first; it also uses an inline guard on
// the root SET_URL, `after` (reconnecting), `invoke` of a callback actor (active), an entry action that writes the
// context (active's clearError), `emit` actions and `reenter`. The chart is by hand, one transition per transition
// of the code (line numbers cite the file above):
//   - the playbackRun callback actor's sendBack (ELEMENT_PLAYING / ENDED / ERROR, MSE_FALLBACK) are events from
//     outside (XState ignores them outside active, as the chart does);
//   - `after: {1200: ...}` in reconnecting is the event RECONNECT (the timer firing), only while reconnecting;
//   - `always: {guard: canConnect, target: active}` in idle (:223) is folded into the transitions that end in idle:
//     only SET_URL's second branch can end there with canConnect true (it gets a twin that enters active);
//   - active's entry clearError (:228) is written by every transition that enters active;
//   - the url (string | null) as maybe(nat): none is null, some(0) the empty string (falsy, :156-157), some(k) a url
//     interned as k; `error` (string | null) as whether it is set.
import {type Maybe, type Term, bool, maybe, nat, no, optional, same, yes} from '../../../core/dsl.ts'
import {chart} from '../../../core/chart.ts'
import {type RealItem, chartLaw, chartStep, leadsTo} from '../lib.ts'

const src = {repo: 'albatrocity/radio-room', commit: 'cefbd86daa0c6eefcfb1ac02b7a725eb2be16ac4', licence: 'MIT', author: 'albatrocity', language: 'TypeScript'}

const MAX_PLAYBACK_RETRIES = 3 // :29
export const events = ['PLAY', 'PAUSE', 'SET_URL', 'TEARDOWN', 'ELEMENT_PLAYING', 'ELEMENT_ENDED', 'ELEMENT_ERROR', 'MSE_FALLBACK', 'RECONNECT'] as const
const all = ['idle', 'active', 'reconnecting', 'failed']
// :156-157 hasUrl: Boolean(context.url)
const hasUrl = (url: Maybe<Term>) => url.match({none: () => no, some: x => x.atLeast(1)})
export const radioStream = () => {
  return chart('radioStream')
    .events(...events)
    .inputs({u: nat}) // SET_URL's url, interned (0: the empty string)
    // :191-197
    .context({url: {kind: maybe(nat), init: null}, playing: {kind: bool, init: false}, hasError: {kind: bool, init: false}, retries: 0, mseRejected: {kind: bool, init: false}})
    .states({idle: {}, active: {states: {loading: {}, playing: {}}}, reconnecting: {}, failed: {}})
    // :199-207 SET_URL (root): [{guard playing && event.url !== context.url, target .active, reenter, setUrl}, {setUrl}]
    .on('SET_URL', {from: all, to: 'active', fresh: true,
      when: ({playing, url, u}) => playing.and(url.match({none: () => yes, some: x => x.eq(u).not()})),
      set: ({u}) => ({url: optional(yes, u), hasError: no, retries: 0})})
    // the second branch, where it ends in idle with canConnect (:223 `always`): into active (playing, and the url it
    // sets is the one it had)
    .on('SET_URL', {from: 'idle', to: 'active', when: ({playing, u}) => playing.and(u.atLeast(1)), set: ({u}) => ({url: optional(yes, u), hasError: no, retries: 0})})
    .on('SET_URL', {from: all, set: ({u}) => ({url: optional(yes, u), hasError: no, retries: 0})})
    // :208 PAUSE → idle, clearPlaying (canConnect is then false)
    .on('PAUSE', {from: all, to: 'idle', set: () => ({playing: no})})
    // :209 TEARDOWN → idle, reset (:176-182)
    .on('TEARDOWN', {from: all, to: 'idle', set: ({u}) => ({url: optional(no, u), playing: no, hasError: no, retries: 0, mseRejected: no})})
    // :213-222 idle PLAY: [{hasUrl → active, setPlaying, clearRetries (and clearError)}, {setPlaying}] (url falsy: canConnect false)
    .on('PLAY', {from: 'idle', to: 'active', when: ({url}) => hasUrl(url), set: () => ({playing: yes, retries: 0, hasError: no})})
    .on('PLAY', {from: 'idle', set: () => ({playing: yes})})
    // :240-243 loading ELEMENT_PLAYING → playing, clearRetries (clears error too, :174), emitPlaybackStarted
    .on('ELEMENT_PLAYING', {from: 'active.loading', to: 'active.playing', set: () => ({retries: 0, hasError: no})})
    // :244, :249 rejectMse
    .on('MSE_FALLBACK', {from: 'active', set: () => ({mseRejected: yes})})
    // :254-257 ELEMENT_ENDED: [{canRetry → reconnecting, countRetry}, {→ failed, setError ("streamFailed"), emitFailed}]
    .on('ELEMENT_ENDED', {from: 'active', to: 'reconnecting', when: ({retries}) => retries.lt(MAX_PLAYBACK_RETRIES), set: ({retries}) => ({retries: retries.plus(1)})})
    .on('ELEMENT_ENDED', {from: 'active', to: 'failed', set: () => ({hasError: yes})})
    // :258-265 ELEMENT_ERROR: [{canRetry → reconnecting, setError, countRetry}, {→ failed, setError, emitFailed}]
    .on('ELEMENT_ERROR', {from: 'active', to: 'reconnecting', when: ({retries}) => retries.lt(MAX_PLAYBACK_RETRIES), set: ({retries}) => ({hasError: yes, retries: retries.plus(1)})})
    .on('ELEMENT_ERROR', {from: 'active', to: 'failed', set: () => ({hasError: yes})})
    // :270-275 after 1200: [{canConnect → active (reenter; entry clearError)}, {→ idle}]
    .on('RECONNECT', {from: 'reconnecting', to: 'active', when: ({playing, url}) => playing.and(hasUrl(url)), set: () => ({hasError: no})})
    .on('RECONNECT', {from: 'reconnecting', to: 'idle'})
    // :279-288 failed PLAY: as idle's
    .on('PLAY', {from: 'failed', to: 'active', when: ({url}) => hasUrl(url), set: () => ({playing: yes, retries: 0, hasError: no})})
    .on('PLAY', {from: 'failed', set: () => ({playing: yes})})
}

const c = radioStream()
const ev = (e: (typeof events)[number]) => events.indexOf(e)
export const items: RealItem[] = [{
  id: 'xstate/radio-room/radioStream',
  domain: 'xstate',
  source: {...src, path: 'apps/web/src/machines/radioStreamMachine.ts', lines: '25-291', export: 'radioStreamMachine'},
  summary: 'A radio stream player: connect on PLAY, reconnect 1.2 s after the element ends or errors, give up after 3 consecutive failures without playback; PAUSE/TEARDOWN back to idle, SET_URL while playing switches streams.',
  expressible: 'partial',
  gaps: [
    {gap: 'async', blocks: 'part', detail: 'invoke of the playbackRun callback actor (its sendBack events come from outside) and `after: {1200: ...}` in reconnecting (the timer firing is the event RECONNECT)'},
    {gap: 'other', blocks: 'part', detail: 'fromXState refuses it: `always` in idle (first; folded by hand into the one transition that can end in idle with canConnect); also an inline guard on the root SET_URL, `after`, `invoke`, an entry action writing the context (active\'s clearError, folded into the transitions entering active), `emit` actions (not modelled), `reenter`'},
    {gap: 'string', blocks: 'part', detail: 'the url (string | null) as maybe(nat), urls interned as numbers and the empty string as 0; the error message as whether one is set'},
  ],
  laws: [
    chartLaw(c, c.law('the retries stay within 3', ({retries}) => retries.atMost(MAX_PLAYBACK_RETRIES)),
      'safety', 'docs', ':28-29 "Consecutive failures without reaching playback before we give up." MAX_PLAYBACK_RETRIES = 3'),
    chartStep(c, c.stepLaw('a fourth consecutive failure gives up', (_, after) => after.in('failed'), b => b.in('active').and(b.retries.eq(MAX_PLAYBACK_RETRIES), b.event.is('ELEMENT_ERROR').or(b.event.is('ELEMENT_ENDED')))),
      'step', 'docs', ':28 "Consecutive failures without reaching playback before we give up"'),
    chartStep(c, c.stepLaw('reaching playback resets the retries', (_, after) => after.retries.eq(0), b => b.in('active.loading').and(b.event.is('ELEMENT_PLAYING'))),
      'step', 'docs', ':28 "Consecutive failures without reaching playback": playback ends the run of failures (:242 clearRetries)'),
    // Stated first as an invariant ("a failed stream has its error set"), it is false: SET_URL with the same url in
    // failed runs setUrl (:162-166), which clears the error and stays in failed (repro/radio-room.ts). A law error, not
    // a bug: the error is reported when failing (emitFailed), which is what the code means.
    chartStep(c, c.stepLaw('a stream fails with its error set', (_, after) => after.hasError, b => b.in('failed').not().and(b.event.is('ELEMENT_ERROR').or(b.event.is('ELEMENT_ENDED')), b.in('active'), b.retries.atLeast(MAX_PLAYBACK_RETRIES))),
      'step', 'inferred', ':256, :264 entering failed runs setError and emitFailed with context.error'),
    chartLaw(c, c.law('the stream connects only with a url', env => env.in('active').implies(hasUrl(env.url))),
      'safety', 'tests', "radioStreamMachine.test.ts:35 'waits for a url before starting the element'; every other way into active is guarded by hasUrl or canConnect (:216, :223, :272, :282)"),
    chartStep(c, c.stepLaw('TEARDOWN drops the stream and forgets the url', (_, after) => after.in('idle').and(after.url.isNone, after.playing.not(), after.retries.eq(0)), b => b.event.is('TEARDOWN')),
      'step', 'docs', ':45 "Player unmounted — drop the stream and forget the url."'),
    chartStep(c, c.stepLaw('an element event outside active changes nothing', (b, after) => after.in('active').not().and(after.retries.eq(b.retries), same(after.hasError, b.hasError), same(after.mseRejected, b.mseRejected)), b => b.in('active').not().and(b.event.is('ELEMENT_ERROR').or(b.event.is('ELEMENT_ENDED'), b.event.is('ELEMENT_PLAYING'), b.event.is('MSE_FALLBACK')))),
      'step', 'inferred', 'the element events are handled only in active (:238-266): elsewhere XState ignores them'),
    leadsTo(c.rule, c.rule.leadsTo('a reconnect wait always ends', {
      from: env => c.in(env, 'reconnecting'),
      to: env => c.in(env, 'reconnecting').not(),
      helpful: () => ({event: ev('RECONNECT')}),
    }), 'docs', ':25 "Element dropped the stream (server hiccup) — wait before reconnecting."; the timer always fires (:270-275, both branches leave)'),
  ],
}]
