// The enumeration as one hand-written u32 kernel: what a writer with 32-bit word operations would emit for
// circuit.ts's program. A world is w = (block << 11) | j, and its atoms are w's bits, so no table reads.
import {createDocumentStore, createKernelRunner, requestBatchDevice} from '../vendor/handwired/src/json-search/gpu/host.ts'
import {compileEmptyPipeline, createReporter, round, sample, summary} from '../vendor/handwired/lab/json-search/gpu/measure.ts'
import type {EnumConfig} from './page.ts'

const code = `
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
const {report, post, log} = createReporter()
const config = await (await fetch('/config')).json() as EnumConfig
const results: Record<string, unknown>[] = []
report['results'] = results
try {
  const largest = Math.max(...config.ks.map(entry => entry.k))
  const {device} = await requestBatchDevice(2 ** (largest - 11) * 4)
  report['emptyPipelineMs'] = round(await compileEmptyPipeline(device, config.salt))
  for (const {k, reachable, violations} of config.ks) {
    const documents = 2 ** (k - 11)
    const store = await createDocumentStore(device, 1, documents)
    const runner = await createKernelRunner(device, {code, workgroupSize: 64, tableLength: 4, cellsPerDocument: 1}, store, config.salt + k)
    const mask = (bits: number) => (bits >= 32 ? 0xffffffff : 2 ** bits - 1)
    const tables = Uint32Array.of((0x55555555 & mask(k)) >>> 0, (0x49249249 & mask(k - 2)) >>> 0, 2 ** (k - 1), 0)
    const first = await runner.evaluate({count: documents, tables})
    let r = 0, v = 0
    for (let d = 0; d < documents; d++) [r, v] = [r + Math.floor(first.counts[d]! / 4096), v + (first.counts[d]! % 4096)]
    const samples = await sample(config, () => runner.evaluate({count: documents}))
    const pass = runner.hasTimestamps ? summary((await sample({...config, minimumSamples: 5, maximumSamples: 20}, () => runner.evaluate({count: documents, timestamps: true}))).map(s => s.passMs)) : undefined
    const entry = {k, agree: r === reachable && v === violations, reachable: r, violations: v, compileMs: round(runner.compileMs), backToBackMs: summary(samples.map(s => s.totalMs)), passMs: pass}
    results.push(entry)
    log(JSON.stringify(entry))
    runner.destroy()
    store.buffer.destroy()
    await post(false)
  }
} catch (error) {
  report['error'] = String(error instanceof Error ? error.stack : error)
  log(`error: ${String(error)}`)
}
await post(true)
