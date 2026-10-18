// The circuit on the CPU at small K, against js.jsonl's counts.
import {createLoopRunner, describeLoop} from '../../vendor/handwired/src/json-search/loop-program.ts'
import {buildEnum, writeBlocks} from './circuit.ts'
for (const k of [16, 20]) {
  const {loop, documents, cellsPerDocument} = buildEnum(k)
  const runner = createLoopRunner(loop, 'generated')
  const cells = writeBlocks(k, documents, cellsPerDocument)
  const out = [new Float32Array(documents * 2)]
  const started = performance.now()
  for (let d = 0; d < documents; d++) runner.run([cells], d, out, d, -1)
  const ms = performance.now() - started
  let r = 0, v = 0
  for (let d = 0; d < documents; d++) [r, v] = [r + out[0]![2 * d]!, v + out[0]![2 * d + 1]!]
  console.log(JSON.stringify({k, reachable: r, violations: v, cpuMs: Math.round(ms), step: describeLoop(loop)}))
}
