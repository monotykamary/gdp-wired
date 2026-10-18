// The enumeration on WebGPU at each K, against the counts in the config (from js.jsonl).
import {emitBitLoopWgsl} from '../../vendor/handwired/src/json-search/bit-emit.ts'
import {createDocumentStore, createProgramRunner, requestBatchDevice} from '../../vendor/handwired/src/json-search/gpu/host.ts'
import {compileEmptyPipeline, createReporter, round, sample, summary} from '../../vendor/handwired/lab/json-search/gpu/measure.ts'
import {buildEnum, writeBlocks} from './circuit.ts'

export type EnumConfig = {ks: {k: number, reachable: number, violations: number}[], salt: number, warmupMs: number, sampleMs: number, minimumSamples: number, maximumSamples: number, cpuWarmupMs: number, cpuSampleMs: number, cpuSamples: number}
const {report, post, log} = createReporter()
const config = await (await fetch('/config')).json() as EnumConfig
const results: Record<string, unknown>[] = []
report['results'] = results
try {
  const largest = Math.max(...config.ks.map(entry => entry.k))
  const {device} = await requestBatchDevice(2 ** (largest - 11) * (largest - 11) * 4)
  report['emptyPipelineMs'] = round(await compileEmptyPipeline(device, config.salt))
  for (const {k, reachable, violations} of config.ks) {
    const fromScratch = performance.now()
    const built = buildEnum(k)
    const shader = emitBitLoopWgsl(built.loop)
    const cells = writeBlocks(k, built.documents, built.cellsPerDocument)
    const store = await createDocumentStore(device, built.cellsPerDocument, built.documents)
    store.write(cells, built.documents)
    const runner = await createProgramRunner(device, shader, built.loop.sharedValues, store, config.salt + k)
    const evaluateOnce = () => runner.evaluate({count: built.documents, readbacks: [{group: 0, firstDocument: 0, documentCount: built.documents}]})
    const first = await evaluateOnce()
    const fromScratchMs = performance.now() - fromScratch
    let r = 0, v = 0
    for (let d = 0; d < built.documents; d++) [r, v] = [r + first.outputs[0]![2 * d]!, v + first.outputs[0]![2 * d + 1]!]
    const samples = await sample(config, evaluateOnce)
    const pass = runner.hasTimestamps ? summary((await sample({...config, minimumSamples: 5, maximumSamples: 20}, () => runner.evaluate({count: built.documents, readbacks: [], timestamps: true}))).map(s => s.passMs)) : undefined
    const entry = {k, agree: r === reachable && v === violations, reachable: r, violations: v, statements: shader.statementCount, compileMs: round(runner.compileMs),
      fromScratchMs: round(fromScratchMs), backToBackMs: summary(samples.map(s => s.totalMs)), passMs: pass}
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
