// The ReBAC and enumeration loop programs on Handwired's CPU loop runner: against next/rebac/fast.ts user by user, and
// against enum/js.jsonl's counts (with `lanes` checked against the laws evaluated atom by atom on random worlds).
import {readFileSync} from 'node:fs'
import {createLoopRunner} from '../../vendor/handwired/src/json-search/loop-program.ts'
import {WordCircuit} from '../../vendor/handwired/src/runtime/words.ts'
import {audit} from '../next/rebac/fast.ts'
import {derive, generate} from '../next/rebac/model.ts'
import {buildEnum, evaluate, lanes, laws} from './enum.ts'
import {CELLS, buildRebac, userCells} from './rebac.ts'

// lanes == the laws atom by atom.
let seed = 9
const rand = () => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return seed }
let worlds = 0, wrong = 0
for (let k = 11; k <= 31; k++) {
  const {reachable, violation} = laws(k)
  const c = new WordCircuit(1), w = c.source(0)
  const roots = [lanes(c, w, reachable), lanes(c, w, violation)]
  for (let n = 0; n < 4000; n++) {
    const world = ((rand() * 2 + (rand() & 1)) >>> 0) & (k >= 32 ? 0xffffffff : 2 ** k - 1)
    const values = c.evaluate(Uint32Array.of(world))
    worlds++
    if (values[roots[0]!] !== (evaluate(reachable, world) ? 1 : 0) || values[roots[1]!] !== (evaluate(violation, world) ? 1 : 0)) wrong++
  }
}
console.log(`lanes: ${worlds} random worlds at k = 11..31, ${wrong} differ from the laws evaluated atom by atom`)

const expected = new Map(readFileSync(new URL('../enum/js.jsonl', import.meta.url), 'utf8').trim().split('\n').map(line => JSON.parse(line)).map((r: {k: number}) => [r.k, r]))
for (const k of [16, 20]) for (const pack of [false, true]) {
  const {loop, documents} = buildEnum(k, pack)
  const runner = createLoopRunner(loop, 'generated')
  const out = [new Float32Array(2)], words = new Uint32Array(out[0]!.buffer)
  let r = 0, v = 0
  for (let d = 0; d < documents; d++) { runner.run([new Float32Array(1)], d, out, 0, -1); r += pack ? words[0]! >>> 12 : words[0]!; v += pack ? words[0]! & 4095 : words[1]! }
  let rr = 0, vv = 0
  for (let world = 0; world < 2 ** k; world++) { const {reachable, violation} = laws(k); void reachable; void violation; if (k > 16) break; rr += evaluate(laws(k).reachable, world) ? 1 : 0; vv += evaluate(laws(k).violation, world) ? 1 : 0 }
  const want = expected.get(k) as {reachable: number, violations: number} | undefined
  console.log(`enum k=${k}${pack ? ' (packed)' : ''}: reachable ${r}, violations ${v}${want ? `; js.jsonl ${want.reachable}, ${want.violations}: ${want.reachable === r && want.violations === v ? 'agree' : 'DIFFER'}` : `; atom by atom ${rr}, ${vv}: ${rr === r && vv === v ? 'agree' : 'DIFFER'}`}`)
}

for (const [stray, pack] of [[true, false], [false, false], [true, true]] as const) {
  const org = generate(3000, 2048, stray, stray ? 3 : 5)
  const d = derive(org)
  const loop = buildRebac(org, d, pack)
  const fast = audit(org, d)
  const cells = userCells(org)
  for (const backend of ['generated', 'executor'] as const) {
    const runner = createLoopRunner(loop, backend)
    const out = [new Float32Array(2)], words = new Uint32Array(out[0]!.buffer)
    const users = backend === 'executor' ? 40 : org.users
    let mismatches = 0, violations = 0
    for (let u = 0; u < users; u++) {
      runner.run([cells], u, out, 0, -1)
      const [seen, bad] = pack ? [words[0]! & 4095, words[0]! >>> 12] : [words[0]!, words[1]!]
      if (seen !== fast.viewable[u] || bad !== fast.violations[u]) mismatches++
      violations += bad
    }
    console.log(`rebac (stray ${stray}${pack ? ', packed' : ''}), ${backend}: ${users} users, ${mismatches} differ from fast.ts, ${violations} violations; ${CELLS} cells per user`)
  }
}
