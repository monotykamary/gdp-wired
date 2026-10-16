// synth/compile-more.ts's kernels (nonincreasing, rankPair, mapRegion, mapKill) as Handwired loop programs of u32 word
// stages, beside hw/synth.ts's history, region and kill. Same layout as there: candidates' coefficients (two's
// complement i32 bits, packForms's order: a pair is two forms, V + 1 numbers each) and alive bits are shared word
// tables, signed comparison flips the sign bit, and a `once` stage loads a kill document's block of 24 candidates into
// registers so the looped stage reads registers, not tables, at every position.
//   nonincreasing  kill over the box: a rank max(0, form − d) dies where the loop runs and it goes up
//   rankPair       kill over the box: a pair (r1, r2) dies where (r1', r2') isn't below (r1, r2) in order
//   mapRegion      document = 24 points, positions walk (point, alive candidate) through a next-alive table; a point is
//                  in the region when every alive candidate holds at k and, read at the written key, at the swapped cell
//   mapKill        kill over the list of region points: a candidate dies where the step breaks it at k
//   guards         document = 24 points: which satisfy the precondition, the assumption and the loop's guard. The rank
//                  kernels run over that list rather than the box: a word stage is straight-line code, so a point where
//                  the loop doesn't run would still pay for its block of candidates (the hand kernel returns early
//                  there). Guards don't depend on the candidates, so the list is built once per evaluator.
// It sits behind synth/more.ts's evaluator interface (moreEvaluator's arguments), so check-synth-more.ts and
// run-synth-more.ts can run either set of kernels on the same rounds.
import {type C, type E} from '../core/machine.ts'
import {type AnyStage, type LoopProgram, type WordBinding, createLoopRunner, createWordStage} from '../vendor/handwired/src/json-search/loop-program.ts'
import {emitLoopWgsl} from '../vendor/handwired/src/json-search/loop-emit.ts'
import {type Word, WordCircuit} from '../vendor/handwired/src/runtime/words.ts'
import {type Box, type Problem, order, points, varsOf} from '../synth/compile.ts'
import type {MapProblem, MoreKind} from '../synth/compile-more.ts'
import type {Evaluator} from '../synth/synth.ts'
import {BLOCK, LIST} from './synth.ts'

type Layout = {sizes: Record<string, number>, at: Record<string, number>}

// inRegisters: a kill document's block is loaded once into registers (hw/synth.ts's pattern); false: read from the table
// at each position, which holds fewer values live when a candidate is wide (a pair is 2 × (V + 1) numbers).
// cb: candidates per kill document (the shader unrolls them; a smaller block compiles faster).
export function compileMoreKernel(p: Problem, box: Box, K: number, kind: MoreKind | 'guards', chunk = 64, inRegisters = kind !== 'rankPair', cb = BLOCK) {
  const V = varsOf(p), F = V.length + 1, width = F * (kind === 'rankPair' ? 2 : 1), A = Math.ceil(K / 32)
  const region = kind === 'mapRegion', guardPass = kind === 'guards'
  const blockRegs = region || guardPass || !inRegisters ? [] : [...Array.from({length: cb}, (_, q) => Array.from({length: width}, (_, i) => `c:${q}:${i}`)).flat(), 'amask']
  // A region document carries its current point's digits in registers (decoded once, then counted up), not decoded
  // from the point's index at every position.
  const regs: string[] = [...(region ? ['q', 'j', 'started', 'mask', ...order(p).map(v => `v:${v}`)] : ['mask']), ...blockRegs]
  const reg = (name: string) => regs.indexOf(name)
  // The coefficient table has one more row, of zeros, for j = K (no candidate left), so a region's reads are in range.
  const tableSizes: [string, number][] = guardPass ? [['base', 1], ['count', 1]] : [['base', 1], ['count', 1], ['coef', (K + 1) * width], ['alive', A]]
  if (region) tableSizes.push(['next', K + 1])
  if (!region && !guardPass) tableSizes.push(['list', LIST]) // every kill runs over a list: region points, or guarded points
  const at: Record<string, number> = {}, sizes: Record<string, number> = {}
  let cell = regs.length + 2 // registers, then position and document
  for (const [name, size] of tableSizes) { at[name] = cell; sizes[name] = size; cell += size }
  const w = new WordCircuit(cell)
  const src = (name: string) => w.source(reg(name))
  const position = w.source(regs.length), document = w.source(regs.length + 1)
  const base = w.source(at.base!), count = w.source(at.count!)
  const k = (n: number) => w.constant(n >>> 0)
  const zero = k(0), one = k(1), S = k(0x80000000)
  const and = (a: Word, b: Word) => w.and(a, b), or = (a: Word, b: Word) => w.or(a, b), not = (a: Word) => w.xor(a, one)
  const sgt = (a: Word, b: Word) => w.lt(w.xor(b, S), w.xor(a, S)) // a > b as i32

  type Env = {vars: Record<string, Word>, flags: Record<string, Word>}
  const ex = (e: E, env: Env): Word => {
    switch (e.op) {
      case 'var': { const v = env.vars[e.name]; if (v === undefined) throw new Error(`unknown variable ${e.name}`); return v }
      case 'const': return k(e.value)
      case 'add': return w.add(ex(e.a, env), ex(e.b, env))
      case 'sub': return w.monus(ex(e.a, env), ex(e.b, env))
      case 'mul': return w.mul(k(e.k), ex(e.a, env))
      case 'prod': return w.mul(ex(e.a, env), ex(e.b, env))
      case 'min': return w.min(ex(e.a, env), ex(e.b, env))
      case 'max': return w.max(ex(e.a, env), ex(e.b, env))
      case 'if': return w.select(cx(e.c, env), ex(e.then, env), ex(e.else, env))
      case 'get': throw new Error('a map read left in a problem: fromMapMachine turns reads into tracked cells')
    }
  }
  const cx = (c: C, env: Env): Word => {
    switch (c.op) {
      case '<': return w.lt(ex(c.a, env), ex(c.b, env))
      case '<=': return w.le(ex(c.a, env), ex(c.b, env))
      case '=': return w.eq(ex(c.a, env), ex(c.b, env))
      case 'and': return c.xs.map(y => cx(y, env)).reduce(and, one)
      case 'or': return c.xs.map(y => cx(y, env)).reduce(or, zero)
      case 'not': return not(cx(c.x, env))
      case 'flag': { const f = env.flags[c.name]; if (f === undefined) throw new Error(`unknown flag ${c.name}`); return f }
    }
  }
  const decode = (index: Word) => {
    const vars: Record<string, Word> = {}
    let rest = index
    for (const v of order(p)) { vars[v] = w.mod(rest, k(box[v]! + 1)); rest = w.div(rest, k(box[v]! + 1)) }
    return vars
  }
  const guardsAt = (vars: Record<string, Word>) => [p.pre, p.assume, p.guard].filter((c): c is C => c !== undefined).map(c => cx(c, {vars, flags: {}})).reduce(and, one)
  const outputs: {wire: Word, write: {kind: 'register', register: number} | {kind: 'stop'}}[] = []
  let positions: number

  if (guardPass) {
    positions = BLOCK
    const point = w.add(base, w.add(w.mul(document, k(BLOCK)), position))
    const ok = and(w.lt(point, count), guardsAt(decode(point)))
    outputs.push({wire: or(src('mask'), w.shl(ok, position)), write: {kind: 'register', register: reg('mask')}})
  } else if (region) {
    // Candidate j's form from the tables, at an environment, and its d.
    const coef = (j: Word, i: number) => w.load(at.coef!, sizes.coef!, w.add(w.mul(j, k(width)), k(i)))
    const form = (j: Word, vars: Record<string, Word>) => V.map((v, i) => w.mul(coef(j, i), vars[v]!)).reduce((a, b) => w.add(a, b), zero)
    positions = BLOCK * (K + 1)
    // Every cell of the next-alive table holds a candidate number, at most K: a contract fill() keeps, so the reads
    // below are written without bounds checks.
    for (let c = 0; c <= K; c++) w.assumeAtMost(w.source(at.next! + c), K)
    w.assumeAtMost(src('j'), K) // the register only ever holds a value read from that table (or its initial 0)
    const q = src('q'), started = src('started')
    const point = w.add(base, w.add(w.mul(document, k(BLOCK)), q)), inPoint = w.lt(point, count)
    const vars: Record<string, Word> = Object.fromEntries(order(p).map(v => [v, src(`v:${v}`)]))
    const guards = guardsAt(vars)
    // The same variables with each map's cell at k replaced by the cell at the key the step writes.
    const swap = (p as MapProblem).swap ?? {}
    const swapped: Record<string, Word> = Object.fromEntries(Object.entries(vars).map(([v, word]) => [v, swap[v] ? vars[swap[v]!]! : word]))
    const jcur = w.select(started, src('j'), w.load(at.next!, K + 1, zero))
    const more = w.lt(jcur, k(K))
    const d = coef(jcur, V.length)
    const breaks = and(more, or(sgt(form(jcur, vars), d), sgt(form(jcur, swapped), d)))
    const end = or(or(not(guards), not(inPoint)), or(not(more), breaks))
    const inRegion = and(and(guards, inPoint), and(not(more), not(breaks)))
    const nextQ = w.select(end, w.add(q, one), q)
    // The next point's digits: count up in the box's mixed radix when this point ends.
    let carry = end
    for (const v of order(p)) {
      const top = w.eq(vars[v]!, k(box[v]!))
      outputs.push({wire: w.select(carry, w.select(top, zero, w.add(vars[v]!, one)), vars[v]!), write: {kind: 'register', register: reg(`v:${v}`)}})
      carry = and(carry, top)
    }
    outputs.push(
      {wire: or(src('mask'), w.shl(and(end, inRegion), q)), write: {kind: 'register', register: reg('mask')}},
      {wire: nextQ, write: {kind: 'register', register: reg('q')}},
      {wire: w.select(end, zero, one), write: {kind: 'register', register: reg('started')}},
      {wire: w.load(at.next!, K + 1, w.min(w.add(jcur, one), k(K))), write: {kind: 'register', register: reg('j')}},
      {wire: or(w.le(k(BLOCK), nextQ), w.le(count, w.add(base, w.add(w.mul(document, k(BLOCK)), nextQ)))), write: {kind: 'stop'}},
    )
  } else {
    positions = chunk
    const nb = Math.ceil(K / cb)
    const chunkIndex = w.div(document, k(nb))
    const slot = w.add(w.mul(chunkIndex, k(chunk)), position)
    // The list's points already satisfy the guards (and, for maps, every alive candidate): only the step is left.
    const valid = w.lt(slot, count) // count: entries in this dispatch's list
    const point = w.load(at.list!, LIST, slot)
    const vars = decode(point)
    const env: Env = {vars, flags: {}}
    for (const [f, c] of Object.entries(p.flags)) env.flags[f] = cx(c, env)
    const after: Record<string, Word> = {...vars, ...Object.fromEntries(p.state.map(v => [v, ex(p.next[v]!, env)]))}
    // Candidate q of the block (from the registers the once stage filled, or the table): slot s's form at an environment
    // and its d.
    const j0 = w.mul(w.mod(document, k(nb)), k(cb))
    const cAt = (q: number, i: number) => (inRegisters ? src(`c:${q}:${i}`) : w.load(at.coef!, sizes.coef!, w.add(w.mul(w.add(j0, k(q)), k(width)), k(i))))
    const amask = inRegisters ? src('amask') : Array.from({length: cb}, (_, q) => { const j = w.add(j0, k(q)); return w.shl(w.and(w.shr(w.load(at.alive!, A, w.shr(j, k(5))), w.and(j, k(31))), one), k(q)) }).reduce(or, zero)
    const bf = (q: number, s: number, vs: Record<string, Word>) => V.map((v, i) => w.mul(cAt(q, s * F + i), vs[v]!)).reduce((a, b) => w.add(a, b), zero)
    const bd = (q: number, s: number) => cAt(q, s * F + V.length)
    // max(0, form − d) as i32: at most 2^31 − 1, so ranks compare as u32.
    const rank = (q: number, s: number, vs: Record<string, Word>) => { const x = w.sub(bf(q, s, vs), bd(q, s)); return w.select(w.shr(x, k(31)), zero, x) }
    const bad = (q: number): Word => {
      if (kind === 'mapKill') return sgt(bf(q, 0, after), bd(q, 0))
      if (kind === 'nonincreasing') return w.lt(rank(q, 0, vars), rank(q, 0, after))
      const r1 = rank(q, 0, vars), r1a = rank(q, 0, after)
      return not(or(w.lt(r1a, r1), and(w.eq(r1a, r1), w.lt(rank(q, 1, after), rank(q, 1, vars)))))
    }
    const mask = Array.from({length: cb}, (_, q) => w.shl(and(w.and(w.shr(amask, k(q)), one), bad(q)), k(q))).reduce(or, zero)
    outputs.push({wire: or(src('mask'), w.select(valid, mask, zero)), write: {kind: 'register', register: reg('mask')}})
  }

  // The once stage of a region program over the box: the document's first point's digits into registers.
  const stages = []
  if (region) {
    const b = new WordCircuit(cell)
    const doc = b.source(regs.length + 1)
    let rest = b.add(b.source(at.base!), b.mul(doc, b.constant(BLOCK)))
    const outs: {wire: Word, write: {kind: 'register', register: number}}[] = []
    for (const v of order(p)) { outs.push({wire: b.mod(rest, b.constant(box[v]! + 1)), write: {kind: 'register', register: reg(`v:${v}`)}}); rest = b.div(rest, b.constant(box[v]! + 1)) }
    stages.push(createWordStage({name: 'first point', repeat: 'once', circuit: b, sharedOffset: 0, bindings: new Map<Word, WordBinding>([[doc, {kind: 'document'}]]), outputs: outs}))
  }
  // The once stage of a kill program: the document's block of 24 candidates and their alive bits into registers.
  if (blockRegs.length > 0) {
    const b = new WordCircuit(cell)
    const doc = b.source(regs.length + 1), j0 = b.mul(b.mod(doc, b.constant(Math.ceil(K / cb))), b.constant(cb))
    const outs: {wire: Word, write: {kind: 'register', register: number}}[] = []
    let amask = b.constant(0)
    for (let q = 0; q < cb; q++) {
      const j = b.add(j0, b.constant(q))
      for (let i = 0; i < width; i++) outs.push({wire: b.load(at.coef!, sizes.coef!, b.add(b.mul(j, b.constant(width)), b.constant(i))), write: {kind: 'register', register: reg(`c:${q}:${i}`)}})
      const bit = b.and(b.shr(b.load(at.alive!, A, b.shr(j, b.constant(5))), b.and(j, b.constant(31))), b.constant(1))
      amask = b.or(amask, b.shl(bit, b.constant(q)))
    }
    outs.push({wire: amask, write: {kind: 'register', register: reg('amask')}})
    stages.push(createWordStage({name: 'block', repeat: 'once', circuit: b, sharedOffset: 0, bindings: new Map<Word, WordBinding>([[doc, {kind: 'document'}]]), outputs: outs}))
  }
  const stage = createWordStage({
    name: kind, repeat: 'forward', circuit: w, sharedOffset: 0,
    bindings: new Map<Word, WordBinding>([
      ...regs.map((_, r) => [w.source(r), {kind: 'register' as const, register: r}] as const),
      [position, {kind: 'position'}], [document, {kind: 'document'}],
    ]),
    outputs,
  })
  const loop: LoopProgram<AnyStage> = {
    positions: positions!, buffers: [{name: 'none', cellsPerDocument: 1}],
    registers: regs.map(name => ({name, initial: 0, type: 'u32' as const})), fields: [],
    outputGroups: [{name: 'mask', kind: 'document', valuesPerDocument: 1, fill: 0, type: 'u32'}],
    stages: [...stages, stage], results: [{group: 0, column: 0, register: reg('mask')}], sharedValues: new Float32Array(cell), lengthCell: undefined,
  }
  return {loop, layout: {sizes, at} as Layout, cb, work: positions! * (region || guardPass ? 1 : cb) * width}
}

function fill(loop: LoopProgram<AnyStage>, layout: Layout, coefs: Int32Array, K: number, alive: Uint32Array, base: number, count: number, list?: ArrayLike<number>) {
  const words = new Uint32Array(loop.sharedValues.buffer, loop.sharedValues.byteOffset, loop.sharedValues.length)
  const {at, sizes} = layout
  words[at.base!] = base >>> 0
  words[at.count!] = count >>> 0
  if (at.coef !== undefined) {
    words.set(new Uint32Array(coefs.buffer, coefs.byteOffset, coefs.length), at.coef)
    words.set(alive.subarray(0, sizes.alive!), at.alive!)
  }
  if (at.next !== undefined) {
    let n = K
    words[at.next + K] = K
    for (let j = K - 1; j >= 0; j--) { if ((alive[j >>> 5]! >>> (j & 31)) & 1) n = j; words[at.next + j] = n }
  }
  if (at.list !== undefined && list) for (let i = 0; i < list.length; i++) words[at.list + i] = list[i]!
  if (at.coef === undefined) return loop.sharedValues
  return loop.sharedValues
}

export type Target = {kind: 'cpu'} | {kind: 'gpu', device: GPUDevice, host: any}

async function runner(target: Target, loop: LoopProgram<AnyStage>, maxDocs: number) {
  if (target.kind === 'cpu') {
    const r = createLoopRunner(loop, 'generated')
    return {
      run: async (shared: Float32Array, docs: number) => {
        r.setShared(shared)
        const all = new Uint32Array(docs), one = [new Float32Array(1)], words = new Uint32Array(one[0]!.buffer)
        for (let d = 0; d < docs; d++) { r.run([new Float32Array(1)], d, one, 0, -1); all[d] = words[0]! }
        return all
      },
      destroy: () => {},
    }
  }
  const store = await target.host.createDocumentStore(target.device, 1, maxDocs)
  const program = await target.host.createProgramRunner(target.device, emitLoopWgsl(loop), loop.sharedValues, store)
  return {
    run: async (shared: Float32Array, docs: number) => {
      const {outputs} = await program.evaluate({count: docs, shared, readbacks: [{group: 0, firstDocument: 0, documentCount: docs}]})
      return new Uint32Array(outputs[0]!.buffer, outputs[0]!.byteOffset, docs).slice()
    },
    destroy: () => { program.destroy(); store.destroy() },
  }
}

// synth/more.ts's moreEvaluator, on Handwired: `kill` is 'mapKill' (then a region pass first), 'nonincreasing' or
// 'rankPair'; coefs in packForms's order.
export async function moreHwEvaluator(target: Target, p: Problem, box: Box, kill: MoreKind, coefs: Int32Array, K: number, chunk = 64, inRegisters?: boolean): Promise<Evaluator> {
  const total = points(p, box)
  if (total >= 2 ** 32) throw new Error('the box has more than 2^32 points')
  const budget = Number(process.env.SYNTH_WORK ?? 4e9), maxDocs = 65535 * 64
  const docsFor = (work: number) => (target.kind === 'cpu' ? maxDocs : Math.max(64, Math.min(maxDocs, Math.floor(budget / work))))
  // Kills are short (rank rounds over a few thousand points; map kills over the region's few points): a block of 8
  // candidates compiles about 2-3× faster than 24, and costs the rounds little.
  const cb = Number(process.env.HW_KILL_BLOCK ?? (kill !== 'mapKill' && total * K > 1e9 ? BLOCK : 8)), nb = Math.ceil(K / cb)
  const unpack = (masks: Uint32Array, killed: Set<number>) => masks.forEach((m, d) => { if (m) for (let q = 0; q < cb; q++) if ((m >>> q) & 1) killed.add((d % nb) * cb + q) })
  const name = `handwired words (${target.kind})`
  // Points (box indices) from a 24-points-a-document pass, then kill over them in lists of LIST.
  const listPass = async (r: Awaited<ReturnType<typeof runner>>, loop: LoopProgram<AnyStage>, layout: Layout, alive: Uint32Array, docsPer: number) => {
    const found: number[] = []
    for (let first = 0; first < total; first += docsPer * BLOCK) {
      const docs = Math.min(docsPer, Math.ceil((total - first) / BLOCK))
      const masks = await r.run(fill(loop, layout, coefs, K, alive, first, total), docs)
      masks.forEach((m, d) => { if (m) for (let q = 0; q < BLOCK; q++) if ((m >>> q) & 1) found.push(first + d * BLOCK + q) })
    }
    return found
  }
  const killOver = async (r: Awaited<ReturnType<typeof runner>>, loop: LoopProgram<AnyStage>, layout: Layout, alive: Uint32Array, list: number[], chunksPer: number) => {
    const killed = new Set<number>()
    for (let from = 0; from < list.length; from += LIST) {
      const part = list.slice(from, from + LIST)
      for (let c = 0; c * chunk < part.length; c += chunksPer) {
        const sub = part.slice(c * chunk, (c + chunksPer) * chunk)
        unpack(await r.run(fill(loop, layout, coefs, K, alive, 0, sub.length, sub), Math.ceil(sub.length / chunk) * nb), killed)
      }
    }
    return killed
  }
  const kl = compileMoreKernel(p, box, K, kill, chunk, inRegisters, cb)
  const killChunks = Math.max(1, Math.min(Math.ceil(LIST / chunk), Math.floor(docsFor(kl.work) / nb)))
  // Runners are created together so their shader compiles overlap.
  const killRunner = runner(target, kl.loop, killChunks * nb)
  if (kill !== 'mapKill') {
    const g = compileMoreKernel(p, box, K, 'guards', chunk)
    const guardDocs = docsFor(BLOCK * 8)
    const [gr, kr] = await Promise.all([runner(target, g.loop, guardDocs), killRunner])
    let guarded: number[] | undefined
    return {
      name,
      round: async alive => {
        guarded ??= await listPass(gr, g.loop, g.layout, alive, guardDocs)
        return [...await killOver(kr, kl.loop, kl.layout, alive, guarded, killChunks)]
      },
      destroy: () => { gr.destroy(); kr.destroy() },
    }
  }
  // Most points stop at their first or second candidate, so a region dispatch is sized for about 2 positions a point:
  // fewer, larger dispatches (each costs a sync, an upload and a readback).
  const regionDocs = docsFor(BLOCK * 2 * (varsOf(p).length + 1))
  const reg = compileMoreKernel(p, box, K, 'mapRegion', chunk)
  const [rr, kr] = await Promise.all([runner(target, reg.loop, regionDocs), killRunner])
  return {
    name,
    round: async alive => {
      const t0 = performance.now(), list = await listPass(rr, reg.loop, reg.layout, alive, regionDocs), t1 = performance.now()
      const killed = await killOver(kr, kl.loop, kl.layout, alive, list, killChunks)
      if (process.env.HW_TIMES) console.log(`    region ${(t1 - t0).toFixed(1)} ms (${list.length} points), kill ${(performance.now() - t1).toFixed(1)} ms`)
      return [...killed]
    },
    destroy: () => { rr.destroy(); kr.destroy() },
  }
}
