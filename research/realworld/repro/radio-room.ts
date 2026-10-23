// Repro: radio-room's radioStreamMachine (albatrocity/radio-room@cefbd86d, MIT), two laws of
// research/realworld/items/xstate-radio.ts:
//   1. "the stream connects only with a url": PLAY (no url yet: idle, playing), SET_URL a url (active), SET_URL ""
//      (the empty string) — the root SET_URL's first branch (:201) enters active without hasUrl;
//   2. "a failed stream has its error set" (as first stated): four failures (failed, error set), then SET_URL with the
//      same url — the second branch's setUrl (:162-166) clears the error and the machine stays in failed. Fetches apps/web/src/machines/radioStreamMachine.ts at the
// pinned commit into a temp dir with its two lib imports stubbed (never reached: playbackRun is replaced the way the
// app's own test does, radioStreamMachine.test.ts:11-27, recording each run's url) and its `xstate` import pointed at
// this repo's xstate (5.33.2; the app asks for ^5.18.2). Prints the state and the url each playback run started with.
//   bun research/realworld/repro/radio-room-empty-url.ts
import {mkdirSync, mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {createActor, fromCallback} from 'xstate'

const commit = 'cefbd86daa0c6eefcfb1ac02b7a725eb2be16ac4'
const dir = mkdtempSync(join(tmpdir(), 'radio-'))
mkdirSync(join(dir, 'machines'), {recursive: true}); mkdirSync(join(dir, 'lib', 'mse'), {recursive: true})
const res = await fetch(`https://raw.githubusercontent.com/albatrocity/radio-room/${commit}/apps/web/src/machines/radioStreamMachine.ts`)
if (!res.ok) throw new Error(`HTTP ${res.status}`)
writeFileSync(join(dir, 'machines', 'radioStreamMachine.ts'), (await res.text()).replaceAll(`from "xstate"`, `from "${Bun.resolveSync('xstate', import.meta.dir)}"`))
const stub = (names: string[]) => names.map(n => `export const ${n} = () => null`).join('\n')
writeFileSync(join(dir, 'lib', 'radioPlaybackElement.ts'), stub(['ensureRadioPlaybackElement', 'playRadioPlayback', 'releaseRadioPlayback', 'setRadioPlaybackUrl']))
writeFileSync(join(dir, 'lib', 'mse', 'radioMseTransport.ts'), stub(['ensureRadioMseElement', 'markRadioMsePlaying', 'playRadioMse', 'releaseRadioMse', 'startRadioMseStream', 'useMseRadioTransport']))
const {radioStreamMachine} = await import(join(dir, 'machines', 'radioStreamMachine.ts'))

const A = 'https://example.com/a.mp3'
const scenario = async (name: string, events: ({type: string, url?: string} | 'wait')[]) => {
  console.log(`== ${name}`)
  const runs: string[] = []
  const actor = createActor(radioStreamMachine.provide({actors: {playbackRun: fromCallback(({input}: {input: {url: string}}) => { runs.push(JSON.stringify(input.url)); return () => {} })}})).start()
  for (const e of events) {
    if (e === 'wait') await new Promise(r => setTimeout(r, 1300)) // the reconnect delay (:26, 1200 ms)
    else actor.send(e)
    const s = actor.getSnapshot()
    console.log(`${JSON.stringify(e)} -> ${JSON.stringify(s.value)}, url ${JSON.stringify(s.context.url)}, playing ${s.context.playing}, retries ${s.context.retries}, error ${JSON.stringify(s.context.error)}`)
  }
  console.log(`playback runs started with: ${runs.join(', ')}`)
  actor.stop()
}
await scenario('an empty url while playing', [{type: 'PLAY'}, {type: 'SET_URL', url: A}, {type: 'SET_URL', url: ''}])
const fail = {type: 'ELEMENT_ERROR', message: 'mediaNetwork'}
await scenario('SET_URL in failed', [{type: 'SET_URL', url: A}, {type: 'PLAY'}, fail, 'wait', fail, 'wait', fail, 'wait', fail, {type: 'SET_URL', url: A}])
