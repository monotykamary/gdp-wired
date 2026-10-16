// The ReBAC audit and the predicate enumeration through the Handwired fork on a GPU (Dawn: Metal on a Mac, Vulkan on
// Linux), against fast.ts / js.jsonl, and with --hand against the hand-written shaders of next/rebac/page.ts and
// enum/kernel-page.ts (copied here verbatim, since those files are browser pages) on the same device.
//   DAWN_MODULE=<webgpu>/index.js bun run-more.ts [--hand] [--out result.json]
import {readFileSync, writeFileSync} from 'node:fs'
import {createDocumentStore, createKernelRunner, createProgramRunner, requestBatchDevice} from '../vendor/handwired/src/json-search/gpu/host.ts'
import {emitLoopWgsl} from '../vendor/handwired/src/json-search/loop-emit.ts'
import {audit} from '../next/rebac/fast.ts'
import {GROUPS, derive, generate} from '../next/rebac/model.ts'
import {buildEnum} from './enum.ts'
import {CELLS, buildRebac, userCells} from './rebac.ts'

const has = (f: string) => process.argv.includes(f), arg = (f: string) => { const i = process.argv.indexOf(f); return i < 0 ? undefined : process.argv[i + 1] }
const dawn = await import(process.env.DAWN_MODULE ?? 'webgpu') as {create: (flags: string[]) => GPU, globals: Record<string, unknown>}
Object.assign(globalThis, dawn.globals)
Object.defineProperty(globalThis.navigator, 'gpu', {value: dawn.create(process.platform === 'linux' ? ['backend=vulkan'] : []), configurable: true})
const batch = await requestBatchDevice(1_000_000 * CELLS * 4)
const device = batch.device
console.log(`adapter ${JSON.stringify(batch.adapterInfo)}`)
const round = (v: number) => Math.round(v * 1000) / 1000
// Median of `n` back-to-back runs after one warm-up.
async function time(run: () => Promise<unknown>, n = 9) {
  await run()
  const times: number[] = []
  for (let i = 0; i < n; i++) { const t0 = performance.now(); await run(); times.push(performance.now() - t0) }
  return round(times.sort((a, b) => a - b)[n >> 1]!)
}
const results: Record<string, unknown>[] = []

// --- ReBAC ----------------------------------------------------------------------------------------------------------
const OBJECTS = 2048
const rebacHand = `
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
{
  const largest = 1_000_000
  const org = generate(largest, OBJECTS, true)
  const d = derive(org)
  const loop = buildRebac(org, d, true)
  const module = emitLoopWgsl(loop)
  const store = await createDocumentStore(device, CELLS, largest)
  store.write(userCells(org), largest)
  const runner = await createProgramRunner(device, module, loop.sharedValues, store)
  let hand: Awaited<ReturnType<typeof createKernelRunner>> | undefined, handTables: Uint32Array | undefined
  if (has('--hand')) {
    handTables = new Uint32Array(4 * OBJECTS + GROUPS + 1)
    handTables.set(d.inherited, 0); handTables.set(Uint32Array.from(d.tin), OBJECTS); handTables.set(Uint32Array.from(d.tout), 2 * OBJECTS); handTables.set(d.underFinance, 3 * OBJECTS); handTables.set(org.sub, 4 * OBJECTS)
    handTables[4 * OBJECTS + GROUPS] = 1 << org.financeGroup
    const cells = new Uint32Array(largest * 3)
    for (let u = 0; u < largest; u++) cells.set([org.userGroups[u]!, org.userGrant[2 * u]! >>> 0, org.userGrant[2 * u + 1]! >>> 0], 3 * u)
    const handStore = await createDocumentStore(device, 3, largest)
    handStore.write(new Float32Array(cells.buffer), largest)
    hand = await createKernelRunner(device, {code: rebacHand, workgroupSize: 64, tableLength: handTables.length, cellsPerDocument: 3}, handStore, 1)
  }
  for (const count of [10_000, 100_000, 1_000_000]) {
    const js0 = performance.now()
    const js = audit({...org, users: count}, d)
    const jsMs = round(performance.now() - js0)
    const {outputs} = await runner.evaluate({count, readbacks: [{group: 0, firstDocument: 0, documentCount: count}]})
    const packed = new Uint32Array(outputs[0]!.buffer, outputs[0]!.byteOffset, count)
    const words = new Uint32Array(2 * count)
    for (let u = 0; u < count; u++) { words[2 * u] = packed[u]! & 4095; words[2 * u + 1] = packed[u]! >>> 12 }
    let mismatches = 0, violations = 0
    for (let u = 0; u < count; u++) { if (words[2 * u] !== js.viewable[u] || words[2 * u + 1] !== js.violations[u]) mismatches++; violations += words[2 * u + 1]! }
    const entry: Record<string, unknown> = {what: 'rebac', users: count, pairs: count * OBJECTS, mismatches, violations, jsMs, statements: module.statementCount,
      handwiredMs: await time(() => runner.evaluate({count, readbacks: [{group: 0, firstDocument: 0, documentCount: count}]}))}
    if (hand) {
      const first = await hand.evaluate({count, tables: handTables})
      let handAgrees = true
      for (let u = 0; u < count; u++) if (first.counts[u] !== words[2 * u + 1]! * 4096 + words[2 * u]!) handAgrees = false
      entry.handAgrees = handAgrees
      entry.handMs = await time(() => hand!.evaluate({count, tables: handTables}))
    }
    results.push(entry)
    console.log(JSON.stringify(entry))
  }
  runner.destroy()
  hand?.destroy()
}

// --- the enumeration ------------------------------------------------------------------------------------------------
const enumHand = `
struct Params { count: u32, a: u32, b: u32, c: u32 }
@group(0) @binding(0) var<uniform> params: Params;
@group(0) @binding(1) var<storage, read> tables: array<u32>;
@group(0) @binding(2) var<storage, read> documents: array<f32>;
@group(0) @binding(3) var<storage, read_write> counts: array<f32>;
@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) id: vec3<u32>) {
  let i: u32 = id.x;
  if (i >= params.count) { return; }
  _ = documents[0];
  let e = tables[0];
  let t = tables[1];
  let top = tables[2];
  var r: u32 = 0u;
  var v: u32 = 0u;
  for (var j: u32 = 0u; j < 2048u; j = j + 1u) {
    let w = (i << 11u) | j;
    let reach = select(0u, 1u, ((w >> 1u) & e & ~w) == 0u);
    let c = w & (w >> 1u) & ~(w >> 2u) & t;
    let c2 = (c & ~1u) | (c & 1u & select(0u, 1u, (w & top) != 0u));
    r = r + reach;
    v = v + (reach & select(0u, 1u, c != 0u) & select(0u, 1u, c2 == 0u));
  }
  counts[i] = f32(r * 4096u + v);
}
`
{
  const expected = new Map(readFileSync(new URL('../enum/js.jsonl', import.meta.url), 'utf8').trim().split('\n').map(line => JSON.parse(line)).map((r: {k: number, reachable: number, violations: number}) => [r.k, r]))
  const store = await createDocumentStore(device, 1, 2 ** 20)
  for (const k of [20, 24, 28, 30, 31]) {
    const {loop, documents} = buildEnum(k, true)
    const module = emitLoopWgsl(loop)
    const runner = await createProgramRunner(device, module, loop.sharedValues, store)
    const evaluate = () => runner.evaluate({count: documents, readbacks: [{group: 0, firstDocument: 0, documentCount: documents}]})
    const {outputs} = await evaluate()
    const packed = new Uint32Array(outputs[0]!.buffer, outputs[0]!.byteOffset, documents)
    let r = 0, v = 0
    for (let d = 0; d < documents; d++) { r += packed[d]! >>> 12; v += packed[d]! & 4095 }
    const want = expected.get(k)!
    const entry: Record<string, unknown> = {what: 'enum', k, worlds: 2 ** k, reachable: r, violations: v, agree: r === want.reachable && v === want.violations, statements: module.statementCount, handwiredMs: await time(evaluate)}
    runner.destroy()
    if (has('--hand')) {
      const mask = (bits: number) => (bits >= 32 ? 0xffffffff : 2 ** bits - 1)
      const tables = Uint32Array.of((0x55555555 & mask(k)) >>> 0, (0x49249249 & mask(k - 2)) >>> 0, 2 ** (k - 1), 0)
      const hand = await createKernelRunner(device, {code: enumHand, workgroupSize: 64, tableLength: 4, cellsPerDocument: 1}, store, 2)
      const first = await hand.evaluate({count: documents, tables})
      let hr = 0, hv = 0
      for (let d = 0; d < documents; d++) { hr += Math.floor(first.counts[d]! / 4096); hv += first.counts[d]! % 4096 }
      entry.handAgrees = hr === r && hv === v
      entry.handMs = await time(() => hand.evaluate({count: documents, tables}))
      hand.destroy()
    }
    results.push(entry)
    console.log(JSON.stringify(entry))
  }
}
const out = arg('--out')
if (out) writeFileSync(out, JSON.stringify({adapter: batch.adapterInfo, results}, null, 1))
process.exit(0)
