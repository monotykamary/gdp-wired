// What fromXState says of each XState machine of research/realworld/items/xstate-*.ts, as shipped: each original
// file is fetched at its pinned commit into a temp dir (its app imports stubbed: none is reached, only the config is
// read), its `xstate` import pointed at this repo's xstate (v5 machines) or at xstate@4.34.0 installed from npm into
// the temp dir (v4 machines), the machine made as the app makes it, and passed to fromXState with no bridge. Prints
// fromXState's refusal (it stops at the first), then every construct in the config that fromXState's documented
// subset leaves out (core/xstate.ts's header), found by walking the config: so the README can rank the language gaps
// that block real XState machines.
//   bun research/realworld/repro/xstate-refusals.ts
import {mkdirSync, mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {dirname, join} from 'node:path'
import {fromXState} from '../../../core/xstate.ts'

const dir = mkdtempSync(join(tmpdir(), 'xstate-refusals-'))
const v5 = Bun.resolveSync('xstate', import.meta.dir)
const npm = Bun.spawnSync(['npm', 'install', '--silent', '--no-audit', '--no-fund', '--prefix', join(dir, 'v4'), 'xstate@4.34.0'])
if (npm.exitCode !== 0) throw new Error(`npm install: ${npm.stderr.toString()}`)
const v4 = join(dir, 'v4', 'node_modules', 'xstate', 'lib', 'index.js')

type Spec = {item: string, repo: string, commit: string, files: string[], xstate: string, stubs?: Record<string, string>, make: (mod: Record<string, unknown>) => unknown}
async function load(s: Spec) {
  const root = join(dir, s.item.replaceAll('/', '_'))
  for (const f of s.files) {
    const res = await fetch(`https://raw.githubusercontent.com/${s.repo}/${s.commit}/${f}`)
    if (!res.ok) throw new Error(`${f}: HTTP ${res.status}`)
    let text = (await res.text()).replaceAll(/from (["'])xstate\1/g, `from "${s.xstate}"`)
    for (const [m, body] of Object.entries(s.stubs ?? {})) {
      const stub = join(root, '_stubs', `${m.replaceAll(/[^a-zA-Z0-9]/g, '_')}.ts`)
      mkdirSync(dirname(stub), {recursive: true}); writeFileSync(stub, body)
      text = text.replaceAll(new RegExp(`from (["'])${m.replaceAll(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\1`, 'g'), `from "${stub}"`)
    }
    mkdirSync(dirname(join(root, f)), {recursive: true}); writeFileSync(join(root, f), text)
  }
  return s.make(await import(join(root, s.files[0]!)))
}

// Every construct outside fromXState's subset, by walking the config.
type Node = Record<string, unknown> & {states?: Record<string, Node>, on?: Record<string, unknown>}
function constructs(config: Node): string[] {
  const out = new Set<string>()
  const list = (x: unknown) => (x === undefined ? [] : Array.isArray(x) ? x : [x])
  const fnName = (f: unknown) => (typeof f === 'function' ? ((f as {type?: string}).type ?? 'a function') : undefined)
  const walk = (n: Node, path: string, depth: number) => {
    const at = path || '(root)'
    for (const k of ['always', 'after', 'invoke', 'onDone']) if (n[k] !== undefined) out.add(`\`${k}\` (${at})`)
    if (n.type === 'parallel' && depth > 0) out.add(`a parallel state below the root (${at})`)
    for (const k of ['entry', 'exit']) for (const a of list(n[k])) {
      if (typeof a === 'function') out.add(`an inline ${k} action ${fnName(a)} (${at})`)
      else out.add(`a named ${k} action (${at}): refused if it writes the context`)
    }
    // the transitions: on, always, after's, invoke's onDone / onError
    const transitions: [string, unknown][] = [...Object.entries(n.on ?? {}), ['always', n.always], ...Object.entries((n.after ?? {}) as object).map(([d, t]) => [`after ${d}`, t] as [string, unknown]),
      ...list(n.invoke).flatMap(i => [['invoke onDone', (i as Node).onDone], ['invoke onError', (i as Node).onError]] as [string, unknown][])]
    for (const [e, spec] of transitions) for (const t of list(spec)) {
      if (!t || typeof t !== 'object') continue
      const o = t as Record<string, unknown>
      // (fromXState reads it now; the scored run was made when it dropped it unrefused)
      if (o.cond !== undefined) out.add(`a v4 \`cond\` guard (${at} on ${e}): read as the guard in a v4 machine`)
      if (typeof o.guard === 'function') out.add(`an inline guard ${fnName(o.guard)} (${at} on ${e})`)
      for (const a of list(o.actions)) {
        if (typeof a === 'function') out.add(`an inline action ${fnName(a)} (${at} on ${e})`)
        else if (a && typeof a === 'object' && typeof (a as {params?: unknown}).params === 'function') out.add(`an action with inline params (${at} on ${e})`)
      }
    }
    for (const [k, kid] of Object.entries(n.states ?? {})) walk(kid, path ? `${path}.${k}` : k, depth + 1)
  }
  walk(config, '', 0)
  return [...out]
}

const nul = (names: string[]) => names.map(n => `export const ${n} = () => null`).join('\n')
const specs: Spec[] = [
  {item: 'xstate/gapless.js/track', repo: 'RelistenNet/gapless.js', commit: 'b9329a2f10868f0ee25b6480fb25a7d3aafcd112', xstate: v5,
    files: ['src/machines/track.machine.ts', 'src/machines/fetchDecode.machine.ts', 'src/types.ts'],
    make: m => (m.createTrackMachine as (c: object) => unknown)({trackUrl: 't', resolvedUrl: 't', skipHEAD: false, playbackType: 'HTML5', webAudioLoadingState: 'NONE', isPlaying: false, scheduledStartContextTime: null, notifiedLookahead: false, fetchStarted: false, pendingPlay: false, seekTarget: 0})},
  {item: 'xstate/electric/pullWakeRunner', repo: 'electric-sql/electric', commit: '3f9809fb0bd894cb74470d434749673492ad7acf', xstate: v5,
    files: ['packages/agents-runtime/src/pull-wake-machine.ts'], make: m => (m.createPullWakeMachine as (e: object) => unknown)({})},
  {item: 'xstate/vef-framework-react/uploader', repo: 'coldsmirk/vef-framework-react', commit: '82b2a9e063a378f7b7da1c5c88633493beb2fbae', xstate: v5,
    files: ['packages/core/src/storage/uploader-machine.ts'], make: m => (m.createUploaderMachine as (d: object) => unknown)({})},
  {item: 'xstate/radio-room/radioStream', repo: 'albatrocity/radio-room', commit: 'cefbd86daa0c6eefcfb1ac02b7a725eb2be16ac4', xstate: v5,
    files: ['apps/web/src/machines/radioStreamMachine.ts'],
    stubs: {'../lib/radioPlaybackElement': nul(['ensureRadioPlaybackElement', 'playRadioPlayback', 'releaseRadioPlayback', 'setRadioPlaybackUrl']), '../lib/mse/radioMseTransport': nul(['ensureRadioMseElement', 'markRadioMsePlaying', 'playRadioMse', 'releaseRadioMse', 'startRadioMseStream', 'useMseRadioTransport'])},
    make: m => m.radioStreamMachine},
  {item: 'xstate/open-decision/websocket', repo: 'open-decision/open-decision', commit: '832e4c9f9f33778222c1c3153aad4060dbc9a26e', xstate: v4,
    files: ['packages/tree/sync/src/websocket.machine.ts'],
    stubs: {'@open-decision/api-client': 'export const APIClient = {}', '@open-decision/type-classes': 'export class ODProgrammerError extends Error {}', 'y-websocket': 'export class WebsocketProvider {}', 'yjs': 'export class Doc {}'},
    make: m => m.websocketMachine},
  {item: 'xstate/amplify-ui/forgotPassword', repo: 'aws-amplify/amplify-ui', commit: '1150de70d59e9f9879693e93d2f8e3dcef464fc7', xstate: v4,
    files: ['packages/ui/src/machines/authenticator/actors/forgotPassword.ts'],
    stubs: {'../../../validators': 'export const runValidators = async () => ({})', '../actions': 'export default {}', '../guards': 'export default {}', '../defaultServices': 'export const defaultServices = {}'},
    make: m => (m.forgotPasswordActor as (o: object) => unknown)({services: {}})},
]
for (const s of specs) {
  console.log(`== ${s.item}`)
  const machine = await load(s) as {config: Node}
  try { fromXState(machine as object); console.log('fromXState: accepted') } catch (e) { console.log(`fromXState: ${(e as Error).message}`) }
  for (const k of constructs(machine.config)) console.log(`  - ${k}`)
}
