// One bounded fixture per fresh process. Also runs against the 84b9 tree.
import {existsSync} from 'node:fs'
import {resolve} from 'node:path'
import {pathToFileURL} from 'node:url'
const root = resolve(process.argv[2]!), mode = process.argv[3]
if (mode !== 'native' && mode !== 'plain') throw new Error('native or plain fixture required')
const load = (path: string) => import(pathToFileURL(resolve(root, path)).href)
const {rule, nat, proveRule} = await load('core/dsl.ts')
const {workLedger} = await load('core/work-admission.ts')
const {countsDump} = await load('core/counts.ts')
const policy = existsSync(resolve(root, 'core/search-policy.ts')) ? await load('core/search-policy.ts') : undefined
const inProxy = (): boolean => policy?.inProxySearch() ?? false
const stepProxyStates: boolean[] = [], phases: string[] = [], nativeProxyStates: boolean[] = []
let r = rule('bounded policy fixture').params({size: nat}).pre(({size}: any) => size.atMost(4)).state({value: 0})
if (mode === 'native') r = r.counts({ones: ({size}: any) => ({below: size, body: () => 1})})
r = r.step(({value}: any) => { stepProxyStates.push(inProxy()); return {value} })
const law = r.law('value remains zero', ({value}: any) => value.atMost(0))
const previous = countsDump.on
countsDump.on = (e: {phase: string}) => { phases.push(e.phase); nativeProxyStates.push(inProxy()) }
let verdict: unknown
try { verdict = proveRule(r, [law], {search: {work: 1_000_000}}) }
finally { countsDump.on = previous }
const snapshot = workLedger.snapshot()
const receipt = {schema: 'section69-bounded-control/v1', mode, verdict, stepProxyStates, phases, nativeProxyStates,
  actual: snapshot.actual, reserved: snapshot.reserved, counters: snapshot.counters,
  endpoints: snapshot.activeEndpoints, rootEpoch: snapshot.rootEpoch, proxyAfter: inProxy()}
console.log(JSON.stringify(receipt, (_k, value) => typeof value === 'bigint' ? String(value) : value))
if (mode === 'native' && (stepProxyStates.some(Boolean) || nativeProxyStates.some(Boolean))) process.exitCode = 1
if (mode === 'plain' && policy && !stepProxyStates.some(Boolean)) process.exitCode = 1
if (receipt.proxyAfter || receipt.endpoints.length) process.exitCode = 1
