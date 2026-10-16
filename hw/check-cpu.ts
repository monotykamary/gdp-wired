// The Handwired loop programs on Handwired's CPU loop runner, against search/compile.ts's per-candidate answers (its
// JS twin, itself checked against the interpreter by search/check-cpu.ts): for sampled documents, the least failing
// (depth, candidate) a document reports must be the least over its candidates by search/'s answer.
import {createLoopRunner} from '../vendor/handwired/src/json-search/loop-program.ts'
import {js, size} from '../search/compile.ts'
import {searches} from '../search/models.ts'
import {compile, decodeBest, setRange} from './compile.ts'

const chunk = 32
let seed = 3
const rand = (n: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor((seed / 2 ** 31) * n) }
for (const s of searches) {
  const loop = compile(s.m, s.law, s.space, chunk)
  const total = size(s.m, s.space), docs = Math.ceil(total / chunk)
  const twin = js(s.m, s.law, s.space)
  for (const backend of ['executor', 'generated'] as const) {
    const runner = createLoopRunner(loop, backend)
    runner.setShared(setRange(loop, 0, total))
    const out = [new Float32Array(1)], words = new Uint32Array(out[0]!.buffer)
    let agree = 0, failing = 0
    const samples = backend === 'executor' ? 150 : 1500
    for (let n = 0; n < samples; n++) {
      const doc = n < 3 ? [0, docs - 1, Math.floor(docs / 2)][n]! : rand(docs)
      runner.run([new Float32Array(1)], doc, out, 0, -1)
      const got = decodeBest(words[0]!, 0, doc, chunk)
      let expected: {depth: number, index: number} | undefined
      for (let o = 0; o < chunk; o++) {
        const index = doc * chunk + o
        if (index >= total) break
        const depth = twin(index)
        if (depth !== 0xffffffff && (!expected || depth < expected.depth)) expected = {depth, index}
      }
      if (expected) failing++
      if (JSON.stringify(got) === JSON.stringify(expected)) agree++
      else if (agree + 3 > n) console.log(`  mismatch at document ${doc}: handwired ${JSON.stringify(got)}, search/ ${JSON.stringify(expected)}`)
    }
    console.log(`${(s.what + ':').padEnd(40)} ${backend.padEnd(9)} ${agree} / ${samples} documents agree (${failing} with a failing candidate)`)
  }
}
