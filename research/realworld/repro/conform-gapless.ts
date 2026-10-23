// Conformance: gapless.js's TrackMachine (RelistenNet/gapless.js@b9329a2f, MIT) against the chart in
// research/realworld/items/xstate-gapless.ts. Fetches the original machine (src/machines/track.machine.ts,
// fetchDecode.machine.ts, src/types.ts) at the pinned commit into a temp dir, points its `xstate` import at this
// repo's xstate (5.33.2; the app asks for ^5.33.3: same major), creates it as Track.ts:190-245 does (the initial
// context, `provide` with the guards and the two context-writing actions Track.ts gives, their environment values
// taken from the event), with the fetchDecode child replaced by an inert machine (its answers, BUFFER_READY etc., are
// events the harness sends). Then:
//   1. what fromXState says of the shipped machine (it refuses it: the inline pieces);
//   2. conforms(chart, original, createActor) on random events, for both playback methods.
//   bun research/realworld/repro/conform-gapless.ts
import {mkdtempSync, mkdirSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {assign, createActor, createMachine} from 'xstate'
import {conforms, fromXState} from '../../../core/xstate.ts'
import {track, trackBridge} from '../items/xstate-gapless.ts'

const commit = 'b9329a2f10868f0ee25b6480fb25a7d3aafcd112'
const dir = mkdtempSync(join(tmpdir(), 'gapless-'))
const xstatePath = Bun.resolveSync('xstate', import.meta.dir)
for (const f of ['src/machines/track.machine.ts', 'src/machines/fetchDecode.machine.ts', 'src/types.ts']) {
  const res = await fetch(`https://raw.githubusercontent.com/RelistenNet/gapless.js/${commit}/${f}`)
  if (!res.ok) throw new Error(`${f}: HTTP ${res.status}`)
  mkdirSync(join(dir, f, '..'), {recursive: true})
  writeFileSync(join(dir, f), (await res.text()).replaceAll(`from 'xstate'`, `from '${xstatePath}'`))
}
const {createTrackMachine} = await import(join(dir, 'src/machines/track.machine.ts'))

// Track.ts:190-201 (the urls as short strings)
const initialContext = {trackUrl: 't', resolvedUrl: 't', skipHEAD: false, playbackType: 'HTML5', webAudioLoadingState: 'NONE', isPlaying: false, scheduledStartContextTime: null, notifiedLookahead: false, fetchStarted: false, pendingPlay: false, seekTarget: 0}
type Ev = {type: string, now?: number, offset?: number, webAudioReady?: boolean}
const original = (webAudioOnly: boolean) => createTrackMachine(initialContext).provide({
  guards: {canPlayWebAudio: ({event}: {event: Ev}) => event.webAudioReady === true, isWebAudioOnly: () => webAudioOnly},
  actors: {fetchDecode: createMachine({})},
  actions: {
    freezePausedTime: assign({seekTarget: ({context, event}: {context: {seekTarget: number}, event: Ev}) => Math.max(event.now ?? 0, context.seekTarget)}),
    syncSeekTargetFromCrossover: assign({seekTarget: ({event}: {event: Ev}) => event.offset ?? 0}),
  },
})

try { fromXState(createTrackMachine(initialContext), trackBridge); console.log('fromXState took the shipped machine') } catch (e) { console.log(`fromXState on the shipped machine: ${(e as Error).message}`) }

const payload = (_: string, rand: (n: number) => number) => ({time: rand(6), when: rand(6), url: ['a', 'b', 't'][rand(3)]!, webAudioReady: rand(2) === 1, now: rand(6), offset: rand(6)})
let bad = false
for (const webAudioOnly of [false, true]) {
  const v = conforms(track(), original(webAudioOnly), createActor as never, {runs: 400, depth: 24, params: {webAudioOnly}, payload})
  console.log(`webAudioOnly=${webAudioOnly}: ${v.checked} steps checked${v.failure ? `; FIRST DIVERGENCE ${v.failure}` : ', no divergence'}`)
  if (v.failure) bad = true
}
process.exit(bad ? 1 : 0)
