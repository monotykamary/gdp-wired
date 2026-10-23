// gapless.js (RelistenNet), the per-track audio machine, XState v5. MIT, (c) 2017-2025 Daniel Saewitz.
// https://github.com/RelistenNet/gapless.js/blob/b9329a2f10868f0ee25b6480fb25a7d3aafcd112/src/machines/track.machine.ts
// (the machine), src/Track.ts:190-245 (the context it starts with and the guards and actions it provides), and
// tests/unit/track.machine.test.ts (the intent of the laws).
//
// A track plays through an HTML5 element until its Web Audio buffer is decoded, then hands over to Web Audio
// mid-stream; a preloaded track waits in `loading`; DEACTIVATE from anywhere lands in idle. START_FETCH (a root
// transition) spawns the fetch-and-decode child once.
//
// The rule is the machine's own config read by `fromXState`. The shipped config is refused as it stands (with no
// bridge, first for the context's strings; with this file's bridge, repro/conform-gapless.ts):
//   - track.machine.ts:166-181, the root START_FETCH runs an inline `assign` and `spawnChild` (refused: "an inline
//     action ... name it in setup({actions})");
//   - track.machine.ts:251, :363, BUFFER_READY's guard `({context}) => context.pendingPlay` is inline (refused: "an
//     inline guard").
// `trackConfig` below is the config with those two named (`startFetch`, `hasPendingPlay`) and nothing else changed;
// research/realworld/repro/conform-gapless.ts runs the chart beside the ORIGINAL machine (fetched at the commit,
// created as Track.ts creates it) on random events and finds no run where they part.
//
// What the rule takes from outside, as the request's payload:
//   - canPlayWebAudio (Track.ts:205) reads the Track object (`this.ctx && this.audioBuffer && this.gainNode`): the
//     request says it as `webAudioReady`; isWebAudioOnly (Track.ts:206) is the playback method fixed when the track
//     is made: the param `webAudioOnly`.
//   - freezePausedTime (Track.ts:284-290) reads the element's current time, syncSeekTargetFromCrossover (Track.ts:
//     258-260) the offset the crossover computed: sent in as `now` and `offset`. Times are float seconds in the code;
//     here whole units.
//   - The spawned fetchDecode child (fetchDecode.machine.ts) answers with BUFFER_READY / BUFFER_ERROR / URL_RESOLVED,
//     which the chart receives as events from outside, in any order; `fetches` (ghost) counts the spawns.
import {bool, max, maybe, nat, no, oneOf, optional, same, str, yes} from '../../../core/dsl.ts'
import {type Bridge, fromXState} from '../../../core/xstate.ts'
import {type RealItem, chartLaw, chartStep, leadsTo} from '../lib.ts'

const src = {repo: 'RelistenNet/gapless.js', commit: 'b9329a2f10868f0ee25b6480fb25a7d3aafcd112', licence: 'MIT', author: 'Daniel Saewitz (RelistenNet)', language: 'TypeScript'}

// track.machine.ts:160-503, with the two inline pieces named. The initial context is Track.ts:190-201 (the urls as
// short strings).
const play = ['setPlayingWebAudio', 'startSourceNode', 'startProgressLoop']
export const trackConfig = {
  id: 'track', initial: 'idle',
  context: {trackUrl: 't', resolvedUrl: 't', skipHEAD: false, playbackType: 'HTML5', webAudioLoadingState: 'NONE', isPlaying: false, scheduledStartContextTime: null, notifiedLookahead: false, fetchStarted: false, pendingPlay: false, seekTarget: 0},
  // :165-183
  on: {START_FETCH: {guard: 'canStartFetch', actions: ['startFetch']}},
  states: {
    // :189-273
    idle: {on: {
      SEEK: {actions: ['setSeekTarget', 'reportProgress']},
      HTML5_ENDED: {actions: ['notifyTrackEnded']},
      DEACTIVATE: {actions: ['pauseHtml5', 'resetHtml5Element', 'resetTiming', 'stopProgressLoop', 'clearScheduleAndLookahead', 'clearPendingPlay', 'clearSeekTarget']},
      ACTIVATE: {actions: ['resetTiming', 'resetHtml5Element', 'clearScheduleAndLookahead', 'clearPendingPlay', 'clearSeekTarget']},
      PLAY: [
        {guard: 'canPlayWebAudio', target: 'webaudio', actions: play},
        {guard: 'isWebAudioOnly', actions: ['setPendingPlay', 'triggerFetchForPendingPlay']},
        {target: 'html5', actions: ['setIsPlaying', 'playHtml5', 'startProgressLoop', 'triggerFetchForPendingPlay']},
      ],
      PLAY_WEBAUDIO: {target: 'webaudio', actions: play},
      SCHEDULE_GAPLESS: {target: 'webaudio', actions: ['setScheduledGapless', 'startScheduledSourceNode']},
      PRELOAD: {target: 'loading'},
      BUFFER_LOADING: {actions: 'setLoadingState'},
      BUFFER_READY: [
        {guard: 'hasPendingPlay', target: 'webaudio', actions: ['clearPendingPlay', ...play, 'notifyBufferReady']},
        {actions: ['setLoadedState', 'notifyBufferReady']},
      ],
      BUFFER_ERROR: {actions: ['setErrorState', 'clearPendingPlay']},
      URL_RESOLVED: {actions: 'setResolvedUrl'},
    }},
    // :277-349
    html5: {on: {
      PAUSE: {actions: ['clearIsPlaying', 'freezePausedTime', 'pauseHtml5', 'stopProgressLoop', 'reportProgress']},
      PLAY: {actions: ['setIsPlaying', 'playHtml5', 'startProgressLoop']},
      BUFFER_LOADING: {actions: 'setLoadingState'},
      PLAY_WEBAUDIO: {target: 'webaudio', actions: 'setPlayingWebAudio'},
      BUFFER_READY: {target: 'webaudio', actions: ['setLoadedState', 'crossoverHtml5ToWebAudio', 'syncSeekTargetFromCrossover', 'setPlaybackTypeWebAudio', 'clearNotifiedLookahead', 'notifyBufferReady']},
      BUFFER_ERROR: {actions: 'setErrorState'},
      SEEK: {actions: ['setSeekTarget', 'seekHtml5', 'reportProgress']},
      LOOKAHEAD_REACHED: {actions: 'setNotifiedLookahead'},
      HTML5_ENDED: {target: 'idle', actions: ['clearIsPlaying', 'stopProgressLoop', 'notifyTrackEnded']},
      ACTIVATE: {target: 'idle', actions: ['clearPlayingAndSchedule', 'pauseHtml5', 'stopProgressLoop', 'resetTiming', 'resetHtml5Element', 'clearSeekTarget']},
      URL_RESOLVED: {actions: 'setResolvedUrl'},
      DEACTIVATE: {target: 'idle', actions: ['clearIsPlaying', 'pauseHtml5', 'resetHtml5Element', 'resetTiming', 'stopProgressLoop', 'clearSeekTarget']},
    }},
    // :353-429
    loading: {on: {
      SEEK: {actions: ['setSeekTarget', 'reportProgress']},
      BUFFER_LOADING: {actions: 'setLoadingState'},
      BUFFER_READY: [
        {guard: 'hasPendingPlay', target: 'webaudio', actions: ['clearPendingPlay', ...play, 'notifyBufferReady']},
        {target: 'idle', actions: ['setLoadedState', 'notifyBufferReady']},
      ],
      BUFFER_ERROR: {target: 'idle', actions: ['setErrorState', 'clearPendingPlay']},
      PLAY: [
        {guard: 'canPlayWebAudio', target: 'webaudio', actions: play},
        {guard: 'isWebAudioOnly', actions: ['setPendingPlay', 'triggerFetchForPendingPlay']},
        {target: 'html5', actions: ['setIsPlaying', 'playHtml5', 'startProgressLoop', 'triggerFetchForPendingPlay']},
      ],
      PLAY_WEBAUDIO: {target: 'webaudio', actions: play},
      SCHEDULE_GAPLESS: {target: 'webaudio', actions: ['setScheduledGapless', 'startScheduledSourceNode']},
      ACTIVATE: {target: 'idle', actions: ['clearPlayingAndSchedule', 'clearPendingPlay', 'resetTiming', 'resetHtml5Element', 'clearSeekTarget']},
      DEACTIVATE: {target: 'idle', actions: ['clearIsPlaying', 'clearPendingPlay', 'resetTiming', 'clearSeekTarget']},
      URL_RESOLVED: {actions: 'setResolvedUrl'},
    }},
    // :433-500
    webaudio: {on: {
      PAUSE: {actions: ['clearIsPlaying', 'freezePausedTime', 'clearScheduledStart', 'stopSourceNode', 'stopProgressLoop', 'reportProgress']},
      PLAY: [{guard: 'canPlayWebAudio', actions: ['setIsPlaying', 'startSourceNode', 'startProgressLoop']}, {actions: 'setIsPlaying'}],
      PLAY_WEBAUDIO: {actions: 'setPlayingWebAudioType'},
      SEEK: {actions: ['setSeekTarget', 'clearScheduledStart', 'seekWebAudio', 'reportProgress']},
      SET_VOLUME: {},
      CANCEL_GAPLESS: {target: 'idle', actions: ['clearPlayingAndSchedule', 'stopSourceNode', 'stopProgressLoop', 'resetTiming', 'clearSeekTarget']},
      LOOKAHEAD_REACHED: {actions: 'setNotifiedLookahead'},
      WEBAUDIO_ENDED: {target: 'idle', actions: ['clearIsPlaying', 'stopProgressLoop', 'notifyTrackEnded']},
      ACTIVATE: {target: 'idle', actions: ['clearPlayingAndSchedule', 'stopSourceNode', 'stopProgressLoop', 'resetTiming', 'resetHtml5Element', 'clearSeekTarget']},
      DEACTIVATE: {target: 'idle', actions: ['clearPlayingAndSchedule', 'stopSourceNode', 'resetTiming', 'resetHtml5Element', 'stopProgressLoop', 'clearSeekTarget']},
    }},
  },
}

// Actions that only touch the audio element, the source node, timers or the queue (side effects): no context.
const effects = ['playHtml5', 'startSourceNode', 'crossoverHtml5ToWebAudio', 'notifyBufferReady', 'startScheduledSourceNode', 'startProgressLoop', 'pauseHtml5', 'stopSourceNode', 'stopProgressLoop', 'reportProgress', 'seekHtml5', 'seekWebAudio', 'resetHtml5Element', 'resetTiming', 'notifyTrackEnded', 'triggerFetchForPendingPlay']
const LOADED = 'LOADED', WEBAUDIO = 'WEBAUDIO', none = optional(no, 0)
export const trackBridge: Bridge = {
  params: {webAudioOnly: bool},
  inputs: {time: nat, when: nat, url: str(), webAudioReady: bool, now: nat, offset: nat},
  context: {
    trackUrl: {kind: str(), init: 't'}, resolvedUrl: {kind: str(), init: 't'}, skipHEAD: {kind: bool, init: false},
    playbackType: {kind: oneOf('HTML5', 'WEBAUDIO'), init: 'HTML5'}, webAudioLoadingState: {kind: oneOf('NONE', 'LOADING', 'LOADED', 'ERROR'), init: 'NONE'},
    scheduledStartContextTime: {kind: maybe(nat), init: null},
    // ghost: the fetchDecode children spawned (track.machine.ts:173), not the code's
    fetches: 0,
  },
  guards: {
    canPlayWebAudio: ({webAudioReady}) => webAudioReady, // Track.ts:205, the Track's buffer and nodes, sent in
    isWebAudioOnly: ({webAudioOnly}) => webAudioOnly, // Track.ts:206
    canStartFetch: ({webAudioLoadingState, fetchStarted}) => webAudioLoadingState.is('NONE').and(fetchStarted.not()), // :89-90
    hasPendingPlay: ({pendingPlay}) => pendingPlay, // :251, :363 (inline in the code)
  },
  actions: {
    ...Object.fromEntries(effects.map(a => [a, null])),
    // :169-180, inline in the code: the assign, then spawnChild (counted)
    startFetch: ({fetches}) => ({webAudioLoadingState: 'LOADING', fetchStarted: yes, fetches: fetches.plus(1)}),
    setSeekTarget: ({time}) => ({seekTarget: time}), // :112-114
    clearSeekTarget: () => ({seekTarget: 0}),
    setPendingPlay: () => ({pendingPlay: yes}),
    clearPendingPlay: () => ({pendingPlay: no}),
    setIsPlaying: () => ({isPlaying: yes}),
    clearIsPlaying: () => ({isPlaying: no}),
    setLoadingState: () => ({webAudioLoadingState: 'LOADING'}),
    setLoadedState: () => ({webAudioLoadingState: LOADED}),
    setErrorState: () => ({webAudioLoadingState: 'ERROR'}),
    clearScheduleAndLookahead: () => ({scheduledStartContextTime: none, notifiedLookahead: no}),
    setPlayingWebAudio: () => ({isPlaying: yes, webAudioLoadingState: LOADED, playbackType: WEBAUDIO}),
    setScheduledGapless: ({when}) => ({isPlaying: yes, webAudioLoadingState: LOADED, playbackType: WEBAUDIO, scheduledStartContextTime: optional(yes, when)}),
    clearPlayingAndSchedule: () => ({isPlaying: no, scheduledStartContextTime: none, notifiedLookahead: no}),
    setNotifiedLookahead: () => ({notifiedLookahead: yes}),
    setResolvedUrl: ({url}) => ({resolvedUrl: url}),
    clearScheduledStart: () => ({scheduledStartContextTime: none}),
    setPlayingWebAudioType: () => ({isPlaying: yes, playbackType: WEBAUDIO}),
    setPlaybackTypeWebAudio: () => ({playbackType: WEBAUDIO}),
    clearNotifiedLookahead: () => ({notifiedLookahead: no}),
    // Track.ts:284-290 `Math.max(current, context.seekTarget)`, the element's current time sent in as `now`
    freezePausedTime: ({now, seekTarget}) => ({seekTarget: max(now, seekTarget)}),
    // Track.ts:258-260, the crossover's offset sent in
    syncSeekTargetFromCrossover: ({offset}) => ({seekTarget: offset}),
  },
}
export const track = () => fromXState(trackConfig, trackBridge)

const c = track()
// An event's index as the chart encodes it (the order fromXState first meets it: the root, then each state's).
const events = [...new Set([trackConfig.on, ...Object.values(trackConfig.states).map(n => n.on)].flatMap(o => Object.keys(o)))]
const ev = (e: string) => events.indexOf(e)
const cite = (path: string, lines: string, exp: string) => ({...src, path, lines, export: exp})
export const items: RealItem[] = [{
  id: 'xstate/gapless.js/track',
  domain: 'xstate',
  source: cite('src/machines/track.machine.ts', '78-504', 'createTrackMachine'),
  also: [cite('src/Track.ts', '188-245', 'Track (the context, guards and actions it provides)'), cite('tests/unit/track.machine.test.ts', '41-471', 'TrackMachine tests')],
  summary: 'Per-track audio playback: HTML5 until the Web Audio buffer is decoded, then a mid-stream hand-over to Web Audio; preloading, gapless scheduling, deactivation back to idle, and a fetch-and-decode child spawned once.',
  expressible: 'partial',
  gaps: [
    {gap: 'other', blocks: 'part', detail: 'fromXState refuses the shipped config: the root START_FETCH runs an inline assign and spawnChild (track.machine.ts:166-181), BUFFER_READY has an inline guard `({context}) => context.pendingPlay` (:251, :363); the rule is the same config with the two named (conform-gapless.ts: no divergence from the original)'},
    {gap: 'async', blocks: 'part', detail: 'spawnChild(fetchDecode): the child\'s replies (BUFFER_READY, BUFFER_ERROR, URL_RESOLVED) arrive as events from outside, in any order and any number of times (the child sends one outcome)'},
    {gap: 'external', blocks: 'part', detail: 'the guard canPlayWebAudio reads the Track object (Track.ts:205: this.ctx && this.audioBuffer && this.gainNode): sent in with the request as webAudioReady'},
    {gap: 'float', blocks: 'part', detail: 'seekTarget, scheduledStartContextTime and the element\'s currentTime (freezePausedTime, Track.ts:284-290) are float seconds: whole units here'},
  ],
  laws: [
    chartStep(c, c.stepLaw('DEACTIVATE from any state lands in idle', (_, after) => after.in('idle'), b => b.event.is('DEACTIVATE')),
      'step', 'tests', "track.machine.test.ts:391 'DEACTIVATE from any playing state always lands in idle'"),
    chartStep(c, c.stepLaw('DEACTIVATE keeps the buffer\'s loading state', (b, after) => same(after.webAudioLoadingState, b.webAudioLoadingState), b => b.event.is('DEACTIVATE')),
      'step', 'tests', "track.machine.test.ts:408 'webAudioLoadingState is never lost through deactivate cycles'"),
    chartLaw(c, c.law('the fetch-and-decode child is spawned at most once', ({fetches}) => fetches.atMost(1)),
      'safety', 'tests', "track.machine.test.ts:438 'guard prevents double-spawn when already LOADING'"),
    chartLaw(c, c.law('Web Audio plays only a loaded buffer', env => env.in('webaudio').implies(env.webAudioLoadingState.is('LOADED'))),
      'safety', 'docs', 'track.machine.ts:4-9 "webaudio: AudioBufferSourceNode is the active output", "as soon as the buffer is ready"'),
    chartLaw(c, c.law('while Web Audio plays the track reports WEBAUDIO', env => env.in('webaudio').implies(env.playbackType.is('WEBAUDIO'))),
      'safety', 'tests', "track.machine.test.ts:76 'full cycle: html5 → BUFFER_READY (crossover) → ... PLAY_WEBAUDIO' expects playbackType WEBAUDIO in webaudio"),
    chartStep(c, c.stepLaw('a buffer ready while preloading never leaves the track in loading', (_, after) => after.in('loading').not(), b => b.in('loading').and(b.event.is('BUFFER_READY'))),
      'step', 'tests', "track.machine.test.ts:228 'BUFFER_READY in loading transitions to idle so track is not stuck'"),
    chartStep(c, c.stepLaw('a buffer error while Web Audio plays changes nothing', (b, after) => after.in('webaudio').and(same(after.webAudioLoadingState, b.webAudioLoadingState), same(after.isPlaying, b.isPlaying)), b => b.in('webaudio').and(b.event.is('BUFFER_ERROR'))),
      'step', 'inferred', 'webaudio (track.machine.ts:433-500) has no BUFFER_ERROR transition: an event the state does not accept'),
    leadsTo(c.rule, c.rule.leadsTo('a pending play starts on Web Audio or is dropped once the buffer is ready', {
      from: ({pendingPlay}) => pendingPlay,
      to: env => env.pendingPlay.not().or(c.in(env, 'webaudio')),
      helpful: () => ({event: ev('BUFFER_READY')}),
    }), 'docs', 'track.machine.ts:47 "pendingPlay: True when PLAY was received in webAudioOnly mode before buffer is ready"; BUFFER_READY with it set starts webaudio (:249-262, :361-372)'),
  ],
}]
