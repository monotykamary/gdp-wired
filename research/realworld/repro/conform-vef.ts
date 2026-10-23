// Conformance: vef-framework-react's uploader machine (coldsmirk/vef-framework-react@82b2a9e0, Apache-2.0) against the
// chart in research/realworld/items/xstate-vef.ts. Fetches packages/core/src/storage/uploader-machine.ts at the pinned
// commit into a temp dir (its `xstate` import pointed at this repo's xstate 5.33.2; the package asks for ^5.32.3),
// creates it with deps whose four promises the harness settles itself, and drives it and the chart with the same
// random events: START (deps.abortRequested() answering `latched`), ABORT, and X_DONE / X_ERROR, which settle the
// pending promise of that phase (if any) and let XState process it. After every event it compares the state and the
// chart's ghost counters with how often the deps were called. Prints the first divergence.
//   bun research/realworld/repro/conform-vef.ts
import {mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {createActor} from 'xstate'
import {uploader, events} from '../items/xstate-vef.ts'

const commit = '82b2a9e063a378f7b7da1c5c88633493beb2fbae'
const dir = mkdtempSync(join(tmpdir(), 'vef-'))
const res = await fetch(`https://raw.githubusercontent.com/coldsmirk/vef-framework-react/${commit}/packages/core/src/storage/uploader-machine.ts`)
if (!res.ok) throw new Error(`HTTP ${res.status}`)
writeFileSync(join(dir, 'uploader-machine.ts'), (await res.text()).replaceAll(`from "xstate"`, `from "${Bun.resolveSync('xstate', import.meta.dir)}"`))
const {createUploaderMachine} = await import(join(dir, 'uploader-machine.ts'))

type Phase = 'prepare' | 'parts' | 'complete' | 'abort'
let x = 1
const rand = (k: number) => { x = (x * 1103515245 + 12345) % 2 ** 31; return Math.floor(x / 2 ** 31 * k) }
const flush = () => new Promise(r => setTimeout(r, 0))
const c = uploader(), r = c.rule, g = r.compiled(), ps = r.encodeParams({} as never)
let checked = 0
for (let run = 0; run < 300; run++) {
  const calls = {prepares: 0, uploads: 0, completes: 0, aborts: 0, failures: 0, kills: 0}
  const pending = new Map<Phase, {resolve: () => void, reject: (e: Error) => void}>()
  let latched = false
  const promise = (p: Phase, count: keyof typeof calls) => () => { calls[count]++; return new Promise<void>((resolve, reject) => pending.set(p, {resolve, reject})) }
  const actor = createActor(createUploaderMachine({
    prepareSession: promise('prepare', 'prepares'), uploadParts: promise('parts', 'uploads'), completeSession: promise('complete', 'completes'), abortSession: promise('abort', 'aborts'),
    killTransport: () => { calls.kills++ }, recordFailure: () => { calls.failures++ }, abortRequested: () => latched,
  })).start()
  let st = g.init(ps)
  const sent: string[] = []
  for (let d = 0; d < 14; d++) {
    const type = events[rand(events.length)]!, isLatched = rand(3) === 0
    sent.push(type === 'START' ? `START{latched:${isLatched}}` : type)
    if (type === 'START') { latched = isLatched; actor.send({type: 'START', plan: {}} as never) } else if (type === 'ABORT') actor.send({type: 'ABORT'})
    else {
      const [phase, how] = type.split('_') as [string, 'DONE' | 'ERROR'], p = ({PREPARE: 'prepare', PARTS: 'parts', COMPLETE: 'complete', ABORT: 'abort'} as const)[phase as 'PREPARE']
      const d0 = pending.get(p)
      if (d0) { pending.delete(p); if (how === 'DONE') d0.resolve(); else d0.reject(new Error('rejected')) }
    }
    await flush()
    st = g.step(ps, st, r.encodeInput({event: type, latched: isLatched} as never))
    const want = r.decode(st) as Record<string, unknown>, got = actor.getSnapshot().value
    const diff = got !== want.state ? `XState is in ${JSON.stringify(got)}, the chart in ${JSON.stringify(want.state)}` : Object.entries(calls).filter(([k, v]) => want[k] !== v).map(([k, v]) => `${k}: the code called it ${v} times, the chart counts ${JSON.stringify(want[k])}`).join('; ')
    if (diff) { console.log(`FIRST DIVERGENCE after ${sent.join(', ')}: ${diff}`); process.exit(1) }
    checked++
  }
}
console.log(`${checked} steps checked, no divergence`)
