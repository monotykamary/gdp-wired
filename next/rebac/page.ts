// The ReBAC audit on WebGPU: per user, the group closure, then every object: how many it can view and how many of
// those break the finance law. One u32 kernel (what the forked Handwired's word operations would emit), against the
// fast JS path, compared user by user.
import {createDocumentStore, createKernelRunner, requestBatchDevice} from '../../vendor/handwired/src/json-search/gpu/host.ts'
import {createReporter, round, sample, summary} from '../../vendor/handwired/lab/json-search/gpu/measure.ts'
import {audit} from './fast.ts'
import {GROUPS, closure, derive, generate} from './model.ts'

const OBJECTS = 2048
const code = `
struct Params { count: u32, a: u32, b: u32, c: u32 }
@group(0) @binding(0) var<uniform> params: Params;
@group(0) @binding(1) var<storage, read> tables: array<u32>;
@group(0) @binding(2) var<storage, read> users: array<u32>;
@group(0) @binding(3) var<storage, read_write> counts: array<f32>;
const O: u32 = ${OBJECTS}u;
@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) id: vec3<u32>) {
  let i: u32 = id.x;
  if (i >= params.count) { return; }
  var groups = users[i * 3u];
  for (var round = 0u; round < 5u; round = round + 1u) {
    var next = groups;
    for (var g = 0u; g < ${GROUPS}u; g = g + 1u) {
      if (((groups >> g) & 1u) == 1u) { next = next | tables[4u * O + g]; }
    }
    groups = next;
  }
  let d0 = users[i * 3u + 1u];
  let d1 = users[i * 3u + 2u];
  var lo0 = 1u; var hi0 = 0u; var lo1 = 1u; var hi1 = 0u;
  if (d0 != 0xffffffffu) { lo0 = tables[O + d0]; hi0 = tables[2u * O + d0]; }
  if (d1 != 0xffffffffu) { lo1 = tables[O + d1]; hi1 = tables[2u * O + d1]; }
  let member = (groups & tables[4u * O + ${GROUPS}u]) != 0u;
  var count = 0u; var bad = 0u;
  for (var o = 0u; o < O; o = o + 1u) {
    let t = tables[O + o];
    let sees = (tables[o] & groups) != 0u || (t >= lo0 && t <= hi0) || (t >= lo1 && t <= hi1);
    if (sees) {
      count = count + 1u;
      if (tables[3u * O + o] == 1u && !member) { bad = bad + 1u; }
    }
  }
  counts[i] = f32(bad * 4096u + count);
}
`
const {report, post, log} = createReporter()
const config = await (await fetch('/config')).json() as {counts: number[]}
const results: Record<string, unknown>[] = []
report['results'] = results
try {
  const largest = Math.max(...config.counts)
  const org = generate(largest, OBJECTS, true)
  const d = derive(org)
  const tables = new Uint32Array(4 * OBJECTS + GROUPS + 1)
  tables.set(d.inherited, 0); tables.set(d.tin, OBJECTS); tables.set(d.tout, 2 * OBJECTS); tables.set(d.underFinance, 3 * OBJECTS); tables.set(org.sub, 4 * OBJECTS)
  tables[4 * OBJECTS + GROUPS] = 1 << org.financeGroup
  const userCells = new Uint32Array(largest * 3)
  for (let u = 0; u < largest; u++) userCells.set([org.userGroups[u]!, org.userGrant[2 * u]! >>> 0, org.userGrant[2 * u + 1]! >>> 0], 3 * u)
  const {device} = await requestBatchDevice(userCells.byteLength)
  const store = await createDocumentStore(device, 3, largest)
  store.write(new Float32Array(userCells.buffer), largest)
  const runner = await createKernelRunner(device, {code, workgroupSize: 64, tableLength: tables.length, cellsPerDocument: 3}, store, Math.floor(Math.random() * 1e9))
  for (const count of config.counts) {
    const sub = {...org, users: count}
    const jsStarted = performance.now()
    const js = audit(sub, d)
    const jsMs = performance.now() - jsStarted
    const first = await runner.evaluate({count, tables})
    let mismatches = 0, violations = 0, viewable = 0, witness: [number, number] | undefined
    for (let u = 0; u < count; u++) {
      const value = first.counts[u]!
      const bad = Math.floor(value / 4096), seen = value % 4096
      if (bad !== js.violations[u] || seen !== js.viewable[u]) mismatches++
      violations += bad
      viewable += seen
      if (bad > 0 && witness === undefined) {
        const groups = closure(org.userGroups[u]!, org.sub)
        for (let o = 0; o < OBJECTS && !witness; o++) if (d.underFinance[o] && (d.inherited[o]! & groups) !== 0) witness = [u, o]
      }
    }
    const samples = await sample({warmupMs: 200, sampleMs: 1000, minimumSamples: 10, maximumSamples: 100, cpuWarmupMs: 0, cpuSampleMs: 0, cpuSamples: 1}, () => runner.evaluate({count}))
    const entry = {users: count, pairs: count * OBJECTS, mismatches, viewable, violations, witness, jsMs: round(jsMs), gpuMs: summary(samples.map(s => s.totalMs))}
    results.push(entry)
    log(JSON.stringify(entry))
    await post(false)
  }
} catch (error) {
  report['error'] = String(error instanceof Error ? error.stack : error)
  log(`error: ${String(error)}`)
}
await post(true)
