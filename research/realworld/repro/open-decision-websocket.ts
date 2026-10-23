// Repro: Open Decision's websocketMachine (open-decision/open-decision@832e4c9f, MIT), two step laws of
// research/realworld/items/xstate-opendecision.ts:
//   1. "CLOSE ends an open connection": OPEN, the token arrives, connected; CLOSE (what TreeContext.tsx:40-42 sends
//      when its effect is cleaned up). Does the machine leave connected, and is the websocket's cleanup run?
//   2. "a synced connection resets the retries": connected, connection.error (retry), reconnected, connection.ready
//      (the provider synced), and so on: how many good reconnects before the machine gives up in error?
// Installs xstate@4.34.0 (the version in the app's yarn.lock) from npm into a temp dir, fetches
// packages/tree/sync/src/websocket.machine.ts at the pinned commit next to it with its app imports stubbed
// (@open-decision/*, y-websocket, yjs: never reached, the services are replaced), and runs it with withConfig: the
// authenticate service resolves at once, the openWebsocket callback service is held by the harness (it calls back
// connection.ready / connection.error itself and counts the cleanups), and retry_delay is 0 ms (only the waiting is
// shortened; the delay's value isn't read by any guard).
//   bun research/realworld/repro/open-decision-websocket.ts
import {mkdirSync, mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'

const commit = '832e4c9f9f33778222c1c3153aad4060dbc9a26e'
const dir = mkdtempSync(join(tmpdir(), 'opendecision-'))
const npm = Bun.spawnSync(['npm', 'install', '--silent', '--no-audit', '--no-fund', '--prefix', dir, 'xstate@4.34.0'])
if (npm.exitCode !== 0) throw new Error(`npm install: ${npm.stderr.toString()}`)
const xstate = join(dir, 'node_modules', 'xstate', 'lib', 'index.js')
const res = await fetch(`https://raw.githubusercontent.com/open-decision/open-decision/${commit}/packages/tree/sync/src/websocket.machine.ts`)
if (!res.ok) throw new Error(`HTTP ${res.status}`)
mkdirSync(join(dir, 'stubs'))
const stubs: Record<string, string> = {
  '@open-decision/api-client': 'export const APIClient = {auth: {getToken: async () => ({data: {token: "t"}})}}',
  '@open-decision/type-classes': 'export class ODProgrammerError extends Error {}',
  'y-websocket': 'export class WebsocketProvider {}',
  'yjs': 'export class Doc {}',
}
let source = (await res.text()).replaceAll(`from "xstate"`, `from "${xstate}"`)
for (const [m, body] of Object.entries(stubs)) {
  const f = join(dir, 'stubs', `${m.replaceAll('/', '_')}.ts`)
  writeFileSync(f, body)
  source = source.replaceAll(`from "${m}"`, `from "${f}"`)
}
writeFileSync(join(dir, 'websocket.machine.ts'), source)
const {websocketMachine} = await import(join(dir, 'websocket.machine.ts'))
const {interpret} = await import(xstate)

const tick = () => new Promise(r => setTimeout(r, 5))
const run = async (name: string, steps: (h: {send: (e: object) => void, socket: (e: string) => void}) => Promise<void>) => {
  console.log(`== ${name}`)
  let callback: ((e: string) => void) | undefined, cleanups = 0
  const machine = websocketMachine.withConfig({
    services: {
      authenticate: async () => ({token: 't'}),
      openWebsocket: () => (cb: (e: string) => void) => { callback = cb; return () => { cleanups++ } },
    },
    delays: {retry_delay: 0},
  })
  const service = interpret(machine).start()
  const show = (what: string) => console.log(`${what.padEnd(22)} -> ${JSON.stringify(service.state.value)}, retries ${service.state.context.retries}, websocket cleanups ${cleanups}`)
  await steps({
    send: e => { service.send(e); show(JSON.stringify(e)) },
    socket: e => { callback?.(e); show(`socket: ${e}`) },
  })
  service.stop()
}
const open = {type: 'OPEN', id: 'tree', yDoc: {}, onSync: () => {}}
await run('CLOSE while connected', async h => {
  h.send(open); await tick(); h.send({type: 'CLOSE'}); await tick(); h.send({type: 'OPEN', id: 'another tree', yDoc: {}, onSync: () => {}})
})
await run('drops, each followed by a good reconnect', async h => {
  h.send(open); await tick()
  for (let i = 0; i < 11; i++) { h.socket('connection.ready'); h.socket('connection.error'); await tick(); await tick() }
})
