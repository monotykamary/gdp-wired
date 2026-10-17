// Step-law searches (step-searches.ts) on Handwired's CPU loop runner, against core/watch.ts reading each candidate's run
// on the interpreter (search/compile.ts's replay), which shares no code with the compiled program: every document's
// least failing (depth, candidate) must be the least over its candidates by the replay, a broken law must turn up a run
// that breaks it, and a proven one none. `generated` runs every document of each space, `executor` a sample.
import type {C, E, Machine} from '../core/machine.ts'
import type {StepLaw} from '../kernel/kernel.ts'
import {proveStepLaws} from '../kernel/prove.ts'
import {createLoopRunner} from '../vendor/handwired/src/json-search/loop-program.ts'
import {replay, size} from '../search/compile.ts'
import {historySearches, stepSearches} from './step-searches.ts'
import {compile, decodeBest, setRange} from './compile.ts'

const chunk = 32
let seed = 5, failed = false
const rand = (n: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor((seed / 2 ** 31) * n) }
for (const s of stepSearches) {
  const loop = compile(s.m, s.law, s.space, chunk)
  const total = size(s.m, s.space), docs = Math.ceil(total / chunk)
  // The replay's answer for every candidate: the depth its run breaks the law at, or none.
  const depthOf = Array.from({length: total}, (_, index) => replay(s.m, s.law, s.space, index)?.trace.length)
  let best: {depth: number, index: number} | undefined
  for (const backend of ['executor', 'generated'] as const) {
    const runner = createLoopRunner(loop, backend)
    runner.setShared(setRange(loop, 0, total))
    const out = [new Float32Array(1)], words = new Uint32Array(out[0]!.buffer)
    const sample = backend === 'generated' ? Array.from({length: docs}, (_, d) => d) : Array.from({length: Math.min(docs, 120)}, (_, n) => (n < 2 ? [0, docs - 1][n]! : rand(docs)))
    let agree = 0
    for (const doc of sample) {
      runner.run([new Float32Array(1)], doc, out, 0, -1)
      const got = decodeBest(words[0]!, 0, doc, chunk)
      let expected: {depth: number, index: number} | undefined
      for (let o = 0; o < chunk && doc * chunk + o < total; o++) {
        const depth = depthOf[doc * chunk + o]
        if (depth !== undefined && (!expected || depth < expected.depth)) expected = {depth, index: doc * chunk + o}
      }
      if (JSON.stringify(got) === JSON.stringify(expected)) agree++
      else if (agree + 3 > sample.length - 3) console.log(`  mismatch at document ${doc}: handwired ${JSON.stringify(got)}, replay ${JSON.stringify(expected)}`)
      if (backend === 'generated' && got && (!best || got.depth < best.depth || (got.depth === best.depth && got.index < best.index))) best = got
    }
    if (agree !== sample.length) failed = true
    console.log(`${(s.what + ':').padEnd(64)} ${backend.padEnd(9)} ${agree} / ${sample.length} documents agree`)
  }
  const found = best ? replay(s.m, s.law, s.space, best.index) : undefined
  const ok = s.breaks ? found !== undefined && found.trace.length === best!.depth : best === undefined
  if (!ok) failed = true
  console.log(`${''.padEnd(64)} ${s.breaks ? (found ? `breaks after ${found.trace.length} steps: params ${JSON.stringify(found.params)}, requests ${JSON.stringify(found.trace)}` : 'BROKEN BUT NOTHING FOUND') : (best ? `PROVEN BUT BROKEN at ${JSON.stringify(best)}` : `nothing breaks it in ${total.toLocaleString()} runs`)}`)
}

// Fuzz: random machines and random laws over one, two and three steps. Handwired's least failing run of every document
// must be the replay's, and a law the kernel proves must have no failing run: the three readings of one description.
const vv = (name: string): E => ({op: 'var', name}), cc = (value: number): E => ({op: 'const', value})
const term = (d: number): E => {
  const r = rand(d <= 0 ? 3 : 7)
  if (r === 0) return vv(['x', 'y', 'a', 'b', 'p'][rand(5)]!)
  if (r === 1) return cc(rand(3))
  if (r === 2) return {op: 'get', map: 'M', key: vv('a')}
  if (r === 3) return {op: 'add', a: term(d - 1), b: term(d - 1)}
  if (r === 4) return {op: 'sub', a: term(d - 1), b: term(d - 1)}
  if (r === 5) return {op: 'min', a: term(d - 1), b: term(d - 1)}
  return {op: 'if', c: {op: rand(2) ? '<=' : '=', a: term(d - 1), b: term(d - 1)}, then: term(d - 1), else: term(d - 1)}
}
const x = vv('x'), y = vv('y'), x1 = vv("x'"), y1 = vv("y'"), a = vv('a'), a2 = vv('a@2')
const forms: C[] = [{op: '<=', a: x, b: x1}, {op: '=', a: x1, b: x}, {op: '<=', a: x1, b: {op: 'add', a: {op: 'add', a: x, b: a}, b: a2}},
  {op: '<=', a: {op: 'add', a: x, b: y}, b: {op: 'add', a: x1, b: y1}}, {op: '<=', a: {op: 'get', map: 'M', key: a}, b: {op: 'get', map: "M'", key: a}},
  {op: 'or', xs: [{op: '<', a: x, b: x1}, {op: '=', a: y1, b: y}]}, {op: '<=', a: y1, b: {op: 'add', a: vv('p'), b: cc(4)}}]
let runs = 0, proven = 0, broken = 0, fuzzDocs = 0, fuzzAgree = 0
for (let trial = 0; trial < 40; trial++) {
  const m: Machine = {name: 'random', params: ['p'], inputs: ['a', 'b'], state: {x: cc(0), y: cc(0)}, maps: {M: 0},
    step: {flags: {f: {op: '<=', a: vv('a'), b: vv('b')}}, state: {x: rand(2) ? {op: 'add', a: x, b: term(1)} : term(2), y: {op: 'if', c: {op: 'flag', name: 'f'}, then: term(2), else: y}},
      maps: {M: {key: vv('a'), value: rand(2) ? {op: 'add', a: {op: 'get', map: 'M', key: vv('a')}, b: term(1)} : term(1)}}},
    ...(rand(3) === 0 ? {assume: {op: '<=', a: vv('a'), b: {op: 'add', a: vv('b'), b: cc(1)}} as C} : {})}
  const form = forms[rand(forms.length)]!, k = form === forms[2] ? 2 + rand(2) : 1 + rand(3)
  const law: StepLaw = {name: `form ${forms.indexOf(form)}`, then: form, steps: k, ...(rand(3) === 0 ? {when: [{op: 'flag', name: 'f'} as C]} : {})}
  const space = {depth: 3, bound: 2}
  let loop
  try { loop = compile(m, law, space, chunk) } catch { continue } // a term past 2^32 at this depth
  const total = size(m, space), docs = Math.ceil(total / chunk)
  const depthOf = Array.from({length: total}, (_, index) => replay(m, law, space, index)?.trace.length)
  const runner = createLoopRunner(loop, 'generated')
  runner.setShared(setRange(loop, 0, total))
  const out = [new Float32Array(1)], words = new Uint32Array(out[0]!.buffer)
  let found = false
  for (let doc = 0; doc < docs; doc++) {
    runner.run([new Float32Array(1)], doc, out, 0, -1)
    const got = decodeBest(words[0]!, 0, doc, chunk)
    let expected: {depth: number, index: number} | undefined
    for (let o = 0; o < chunk && doc * chunk + o < total; o++) {
      const depth = depthOf[doc * chunk + o]
      if (depth !== undefined && (!expected || depth < expected.depth)) expected = {depth, index: doc * chunk + o}
    }
    fuzzDocs++
    if (JSON.stringify(got) === JSON.stringify(expected)) fuzzAgree++
    else { failed = true; console.log(`  fuzz mismatch: ${JSON.stringify(m.step)} ${law.name} over ${k}: handwired ${JSON.stringify(got)}, replay ${JSON.stringify(expected)}`) }
    if (got) found = true
  }
  runs += total
  const kernel = proveStepLaws(m, [], [law])
  if (kernel.proven && kernel.checked) { proven++; if (found) { failed = true; console.log(`  UNSOUND? the kernel proves ${law.name} over ${k} on ${JSON.stringify(m.step)}, and a run breaks it`) } }
  if (found) broken++
}
console.log(`fuzz: ${fuzzAgree} / ${fuzzDocs} documents agree over ${runs.toLocaleString()} runs; ${proven} laws the kernel proves (none broken by a run), ${broken} broken by a run`)

// Histories: every example rule with a log, the queries computed from the log in registers. Each law of each variant is
// searched over its whole space; every document must agree with the replay, a proven rule must have no breaking run,
// and a broken variant one for some law.
const budget = Number(process.env.HISTORY_BUDGET ?? 150_000)
for (const hs of historySearches(budget)) {
  const total = size(hs.m, hs.space), docs = Math.ceil(total / chunk)
  let agree = 0, compared = 0
  const found: string[] = []
  for (const law of hs.laws) {
    const loop = compile(hs.m, law, hs.space, chunk)
    const runner = createLoopRunner(loop, 'generated')
    runner.setShared(setRange(loop, 0, total))
    const out = [new Float32Array(1)], words = new Uint32Array(out[0]!.buffer)
    const depthOf = Array.from({length: total}, (_, index) => replay(hs.m, law, hs.space, index)?.trace.length)
    let best: {depth: number, index: number} | undefined
    for (let doc = 0; doc < docs; doc++) {
      runner.run([new Float32Array(1)], doc, out, 0, -1)
      const got = decodeBest(words[0]!, 0, doc, chunk)
      let expected: {depth: number, index: number} | undefined
      for (let o = 0; o < chunk && doc * chunk + o < total; o++) {
        const depth = depthOf[doc * chunk + o]
        if (depth !== undefined && (!expected || depth < expected.depth)) expected = {depth, index: doc * chunk + o}
      }
      compared++
      if (JSON.stringify(got) === JSON.stringify(expected)) agree++
      else if (compared - agree <= 2) console.log(`  mismatch: ${hs.what}: ${law.name}, document ${doc}: handwired ${JSON.stringify(got)}, replay ${JSON.stringify(expected)}`)
      if (got && (!best || got.depth < best.depth || (got.depth === best.depth && got.index < best.index))) best = got
    }
    if (best) { const r = replay(hs.m, law, hs.space, best.index)!; found.push(`${law.name} after ${r.trace.length}: ${JSON.stringify(r.params)} ${JSON.stringify(r.trace)}`) }
  }
  const ok = agree === compared && (hs.breaks ? found.length > 0 : found.length === 0)
  if (!ok) failed = true
  console.log(`${(hs.what + ':').padEnd(72)} ${agree} / ${compared} agree, ${total.toLocaleString()} runs (depth ${hs.space.depth}), ${found.length ? `broken: ${found[0]}` : 'nothing breaks it'}${ok ? '' : '   UNEXPECTED'}`)
}
if (failed) process.exit(1)
