// The table's GPU passes, as Handwired loop programs of u32 word stages (vendor/handwired, branch u32-words), run by
// Handwired's CPU loop runner (the twin) and by its WGSL writer and program runner on a GPU (Dawn). Nothing here is
// trusted: every caller checks what a pass returns against the exact CPU computation (table.ts, ari.ts's evaluator)
// and counts any difference between the GPU and the twin as a bug.
//   columns  Q2's bounds and Q4's fingerprints of sparse linear columns (at most 4 terms each) over the rows: a document
//            is a block of CB columns × a chunk of CH rows; registers carry each column's min and max (i32, compared
//            with the sign bit flipped) and two fingerprints Σ w_r·(v_r mod p) mod p (p = 65521, 65519; the row weights
//            a table), which add across chunks
//   implies  Q5 on 0/1 columns as bitsets (32 rows a word): a document is one atom a × a block of CB atoms b;
//            positions walk the words; register q holds OR of (A & ~B_q), zero exactly when a → b on every row
//   box      guard-solved sampling for a termination rule: a document is 32 points of a box of values (state and the
//            rule's free values, each in −B..B; the values its equations define computed, not enumerated); the guard
//            as a word circuit (i32 wrapping arithmetic); output: the document's mask of points where it holds
import {type AnyStage, type LoopProgram, type WordBinding, createLoopRunner, createWordStage} from '../../vendor/handwired/src/json-search/loop-program.ts'
import {emitLoopWgsl} from '../../vendor/handwired/src/json-search/loop-emit.ts'
import {type Word, WordCircuit} from '../../vendor/handwired/src/runtime/words.ts'

export type Target = {kind: 'cpu'} | {kind: 'gpu', device: GPUDevice, host: any, adapter: unknown}
export async function gpuTarget(): Promise<Target> {
  const dawn = await import(process.env.DAWN_MODULE ?? 'webgpu') as {create: (flags: string[]) => GPU, globals: Record<string, unknown>}
  Object.assign(globalThis, dawn.globals)
  Object.defineProperty(globalThis.navigator, 'gpu', {value: dawn.create(process.platform === 'linux' ? ['backend=vulkan'] : []), configurable: true})
  const host = await import('../../vendor/handwired/src/json-search/gpu/host.ts')
  const batch = await host.requestBatchDevice(65535 * 64 * 4 * 32)
  return {kind: 'gpu', device: batch.device, host, adapter: batch.adapterInfo}
}

// A loop program on a target: run documents 0..docs−1 with the given shared values; the output group's words back.
export async function runnerOf(target: Target, loop: LoopProgram<AnyStage>, maxDocs: number, valuesPerDoc: number) {
  if (target.kind === 'cpu') {
    const r = createLoopRunner(loop, 'generated')
    return {
      run: async (shared: Float32Array, docs: number) => {
        r.setShared(shared)
        const out = new Uint32Array(docs * valuesPerDoc), one = [new Float32Array(valuesPerDoc)], words = new Uint32Array(one[0]!.buffer)
        for (let d = 0; d < docs; d++) { r.run([new Float32Array(1)], d, one, 0, -1); out.set(words, d * valuesPerDoc) }
        return out
      },
      destroy: () => {},
    }
  }
  const store = await target.host.createDocumentStore(target.device, 1, maxDocs)
  const program = await target.host.createProgramRunner(target.device, emitLoopWgsl(loop), loop.sharedValues, store)
  return {
    run: async (shared: Float32Array, docs: number) => {
      const {outputs} = await program.evaluate({count: docs, shared, readbacks: [{group: 0, firstDocument: 0, documentCount: docs}]})
      return new Uint32Array(outputs[0]!.buffer, outputs[0]!.byteOffset, docs * valuesPerDoc).slice()
    },
    destroy: () => { program.destroy(); store.destroy() },
  }
}

const P1 = 65521, P2 = 65519
type Out = {wire: Word, write: {kind: 'register', register: number} | {kind: 'stop'}}

// --- columns ---------------------------------------------------------------------------------------------------------------
// A sparse linear column: up to 4 (variable index, coefficient) terms.
export type SparseCol = {idx: number[], coef: number[]}
export function columnsProgram(V: number, Rmax: number, K: number, CB = 8, CH = 256, T = 4) {
  const nb = Math.ceil(K / CB)
  const regs: string[] = []
  for (let q = 0; q < CB; q++) regs.push(`mn${q}`, `mx${q}`, `h1${q}`, `h2${q}`)
  for (let q = 0; q < CB; q++) for (let t = 0; t < T; t++) regs.push(`i${q}:${t}`, `c${q}:${t}`)
  const reg = (n: string) => regs.indexOf(n)
  const bound = regs.length + 2
  const at = {count: bound, rows: bound + 1, cols: bound + 1 + Rmax * V, w1: bound + 1 + Rmax * V + K * 2 * T, w2: bound + 1 + Rmax * V + K * 2 * T + Rmax}
  const cells = at.w2 + Rmax
  const w = new WordCircuit(cells)
  const k = (n: number) => w.constant(n >>> 0), S = k(0x80000000)
  const src = (n: string) => w.source(reg(n)), position = w.source(regs.length), document = w.source(regs.length + 1)
  const chunk = w.div(document, k(nb)), row = w.add(w.mul(chunk, k(CH)), position)
  const valid = w.lt(row, w.source(at.count))
  const outs: Out[] = []
  const w1 = w.load(at.w1, Rmax, row), w2 = w.load(at.w2, Rmax, row)
  for (let q = 0; q < CB; q++) {
    let v = k(0)
    for (let t = 0; t < T; t++) {
      const x = w.load(at.rows, Rmax * V, w.add(w.mul(row, k(V)), src(`i${q}:${t}`)))
      v = w.add(v, w.mul(src(`c${q}:${t}`), x))
    }
    const f = w.xor(v, S)
    outs.push({wire: w.select(valid, w.min(src(`mn${q}`), f), src(`mn${q}`)), write: {kind: 'register', register: reg(`mn${q}`)}})
    outs.push({wire: w.select(valid, w.max(src(`mx${q}`), f), src(`mx${q}`)), write: {kind: 'register', register: reg(`mx${q}`)}})
    outs.push({wire: w.select(valid, w.mod(w.add(src(`h1${q}`), w.mod(w.mul(w.mod(v, k(P1)), w1), k(P1))), k(P1)), src(`h1${q}`)), write: {kind: 'register', register: reg(`h1${q}`)}})
    outs.push({wire: w.select(valid, w.mod(w.add(src(`h2${q}`), w.mod(w.mul(w.mod(v, k(P2)), w2), k(P2))), k(P2)), src(`h2${q}`)), write: {kind: 'register', register: reg(`h2${q}`)}})
  }
  const stage = createWordStage({name: 'columns', repeat: 'forward', circuit: w, sharedOffset: 0,
    bindings: new Map<Word, WordBinding>([...regs.map((_, r) => [w.source(r), {kind: 'register' as const, register: r}] as const), [position, {kind: 'position'}], [document, {kind: 'document'}]]), outputs: outs})
  // once: the block's columns into registers
  const b = new WordCircuit(cells)
  const doc = b.source(regs.length + 1), j0 = b.mul(b.mod(doc, b.constant(nb)), b.constant(CB))
  const bouts: Out[] = []
  for (let q = 0; q < CB; q++) for (let t = 0; t < T; t++) {
    const j = b.add(j0, b.constant(q)), base = b.mul(j, b.constant(2 * T))
    bouts.push({wire: b.load(at.cols, K * 2 * T, b.add(base, b.constant(2 * t))), write: {kind: 'register', register: reg(`i${q}:${t}`)}})
    bouts.push({wire: b.load(at.cols, K * 2 * T, b.add(base, b.constant(2 * t + 1))), write: {kind: 'register', register: reg(`c${q}:${t}`)}})
  }
  const once = createWordStage({name: 'block', repeat: 'once', circuit: b, sharedOffset: 0, bindings: new Map<Word, WordBinding>([[doc, {kind: 'document'}]]), outputs: bouts})
  const vpd = 4 * CB
  const loop: LoopProgram<AnyStage> = {
    positions: CH, buffers: [{name: 'none', cellsPerDocument: 1}],
    registers: regs.map(name => ({name, initial: name.startsWith('mn') ? 0xffffffff : 0, type: 'u32' as const})), fields: [],
    outputGroups: [{name: 'out', kind: 'document', valuesPerDocument: vpd, fill: 0, type: 'u32'}],
    stages: [once, stage], results: Array.from({length: vpd}, (_, c) => ({group: 0, column: c, register: c})),
    sharedValues: new Float32Array(cells), lengthCell: undefined,
  }
  // the shared values for rows (R × V, i32) and columns; weights from a seeded generator
  const fill = (rows: Int32Array, R: number, cols: SparseCol[]) => {
    const u = new Uint32Array(loop.sharedValues.buffer)
    u[at.count] = R
    u.set(new Uint32Array(rows.buffer, rows.byteOffset, R * V), at.rows)
    cols.forEach((c, j) => { for (let t = 0; t < T; t++) { u[at.cols + j * 2 * T + 2 * t] = c.idx[t] ?? 0; u[at.cols + j * 2 * T + 2 * t + 1] = (c.coef[t] ?? 0) >>> 0 } })
    let x = 12345
    for (let r = 0; r < Rmax; r++) { x = (Math.imul(x, 1103515245) + 12345) >>> 0; u[at.w1 + r] = (x >>> 8) % P1; x = (Math.imul(x, 1103515245) + 12345) >>> 0; u[at.w2 + r] = (x >>> 8) % P2 }
    return loop.sharedValues
  }
  const weights = () => { const u = new Uint32Array(loop.sharedValues.buffer); return {w1: u.slice(at.w1, at.w1 + Rmax), w2: u.slice(at.w2, at.w2 + Rmax)} }
  return {loop, fill, weights, nb, CB, CH, vpd, docs: (R: number) => Math.ceil(R / CH) * nb}
}
// The documents' outputs, combined over chunks: per column lo, hi (i32), h1, h2
export function combineColumns(out: Uint32Array, K: number, nb: number, CB: number, docs: number) {
  const lo = new Int32Array(K).fill(0x7fffffff), hi = new Int32Array(K).fill(-0x80000000), h1 = new Uint32Array(K), h2 = new Uint32Array(K)
  for (let d = 0; d < docs; d++) {
    const block = d % nb
    for (let q = 0; q < CB; q++) {
      const j = block * CB + q
      if (j >= K) continue
      const o = d * 4 * CB + 4 * q, mn = (out[o]! ^ 0x80000000) | 0, mx = (out[o + 1]! ^ 0x80000000) | 0
      if (out[o] !== 0xffffffff && mn < lo[j]!) lo[j] = mn
      if (mx > hi[j]! && !(out[o + 1] === 0 && out[o] === 0xffffffff)) hi[j] = mx
      h1[j] = (h1[j]! + out[o + 2]!) % P1; h2[j] = (h2[j]! + out[o + 3]!) % P2
    }
  }
  return {lo, hi, h1, h2}
}
// The same on the CPU in plain JavaScript over typed arrays (i32 wrapping, as the words): the reference the GPU's
// outputs are compared with, and the CPU time beside the GPU's
export function columnsJs(rows: Int32Array, R: number, V: number, cols: SparseCol[], w1: Uint32Array, w2: Uint32Array) {
  const K = cols.length, lo = new Int32Array(K), hi = new Int32Array(K), h1 = new Uint32Array(K), h2 = new Uint32Array(K)
  for (let j = 0; j < K; j++) {
    const c = cols[j]!
    let mn = 0x7fffffff, mx = -0x80000000, a = 0, b = 0
    for (let r = 0; r < R; r++) {
      let v = 0
      for (let t = 0; t < c.idx.length; t++) v = (v + Math.imul(c.coef[t]!, rows[r * V + c.idx[t]!]!)) | 0
      if (v < mn) mn = v
      if (v > mx) mx = v
      const u = v >>> 0
      a = (a + ((u % P1) * w1[r]!) % P1) % P1
      b = (b + ((u % P2) * w2[r]!) % P2) % P2
    }
    lo[j] = mn; hi[j] = mx; h1[j] = a; h2[j] = b
  }
  return {lo, hi, h1, h2}
}

// --- implies ----------------------------------------------------------------------------------------------------------------
export function impliesProgram(NA: number, NW: number, CB = 32) {
  const nb = Math.ceil(NA / CB)
  const regs = Array.from({length: CB}, (_, q) => `acc${q}`)
  const bound = regs.length + 2, at = {bits: bound}, cells = bound + NA * NW
  const w = new WordCircuit(cells)
  const k = (n: number) => w.constant(n >>> 0)
  const position = w.source(regs.length), document = w.source(regs.length + 1)
  const a = w.div(document, k(nb)), b0 = w.mul(w.mod(document, k(nb)), k(CB))
  const wa = w.load(at.bits, NA * NW, w.add(w.mul(a, k(NW)), position))
  const outs: Out[] = regs.map((r, q) => ({wire: w.or(w.source(q), w.and(wa, w.not(w.load(at.bits, NA * NW, w.add(w.mul(w.add(b0, k(q)), k(NW)), position))))), write: {kind: 'register' as const, register: q}}))
  const stage = createWordStage({name: 'implies', repeat: 'forward', circuit: w, sharedOffset: 0,
    bindings: new Map<Word, WordBinding>([...regs.map((_, r) => [w.source(r), {kind: 'register' as const, register: r}] as const), [position, {kind: 'position'}], [document, {kind: 'document'}]]), outputs: outs})
  const loop: LoopProgram<AnyStage> = {
    positions: NW, buffers: [{name: 'none', cellsPerDocument: 1}],
    registers: regs.map(name => ({name, initial: 0, type: 'u32' as const})), fields: [],
    outputGroups: [{name: 'out', kind: 'document', valuesPerDocument: CB, fill: 0, type: 'u32'}],
    stages: [stage], results: regs.map((_, q) => ({group: 0, column: q, register: q})), sharedValues: new Float32Array(cells), lengthCell: undefined,
  }
  const fill = (bits: Uint32Array) => { new Uint32Array(loop.sharedValues.buffer).set(bits, at.bits); return loop.sharedValues }
  return {loop, fill, nb, CB, docs: NA * nb}
}
export function impliesJs(bits: Uint32Array, NA: number, NW: number): Uint8Array {
  const out = new Uint8Array(NA * NA)
  for (let a = 0; a < NA; a++) for (let b = 0; b < NA; b++) { let acc = 0; for (let i = 0; i < NW; i++) acc |= bits[a * NW + i]! & ~bits[b * NW + i]!; out[a * NA + b] = acc ? 0 : 1 }
  return out
}

// --- box ---------------------------------------------------------------------------------------------------------------------
// A guard over integer variables (ARI's Sx), as words: i32 two's complement, wrapping; signed comparisons by flipping
// the sign bit. `div`/`mod` aren't written (the caller keeps such a rule on the CPU).
export type Sx = string | Sx[]
export class NoWords extends Error {}
export function boxProgram(enumerated: string[], defined: [string, Sx][], guard: Sx, B: number) {
  const regs = ['mask']
  const bound = regs.length + 2, at = {base: bound, count: bound + 1}, cells = bound + 2
  const w = new WordCircuit(cells)
  const k = (n: number) => w.constant(n >>> 0), S = k(0x80000000), one = k(1), zero = k(0)
  const position = w.source(regs.length), document = w.source(regs.length + 1)
  const point = w.add(w.source(at.base), w.add(w.mul(document, k(32)), position))
  const env = new Map<string, Word>()
  let rest = point
  for (const v of enumerated) { env.set(v, w.sub(w.mod(rest, k(2 * B + 1)), k(B))); rest = w.div(rest, k(2 * B + 1)) }
  const slt = (a: Word, b: Word) => w.lt(w.xor(a, S), w.xor(b, S)), sle = (a: Word, b: Word) => w.le(w.xor(a, S), w.xor(b, S))
  const int = (s: Sx): Word => {
    if (typeof s === 'string') {
      if (/^\d+$/.test(s)) { const n = Number(s); if (n > 0x7fffffff) throw new NoWords('a constant past i32'); return k(n) }
      const v = env.get(s)
      if (v === undefined) throw new NoWords(`no value for ${s}`)
      return v
    }
    const [op, ...xs] = s as [string, ...Sx[]]
    switch (op) {
      case '+': return xs.map(int).reduce((a, b) => w.add(a, b), zero)
      case '-': return xs.length === 1 ? w.sub(zero, int(xs[0]!)) : xs.slice(1).map(int).reduce((a, b) => w.sub(a, b), int(xs[0]!))
      case '*': return xs.map(int).reduce((a, b) => w.mul(a, b), one)
      case 'ite': return w.select(bool(xs[0]!), int(xs[1]!), int(xs[2]!))
      case 'abs': { const x = int(xs[0]!); return w.select(slt(x, zero), w.sub(zero, x), x) }
      default: throw new NoWords(`the operator ${op}`)
    }
  }
  const bool = (s: Sx): Word => {
    if (s === 'true') return one
    if (s === 'false') return zero
    if (typeof s === 'string') throw new NoWords(`a condition ${s}`)
    const [op, ...xs] = s as [string, ...Sx[]]
    const pair = (f: (a: Word, b: Word) => Word) => { const v = xs.map(int); return v.slice(1).map((b, i) => f(v[i]!, b)).reduce((a, b) => w.and(a, b), one) }
    switch (op) {
      case 'and': return xs.map(bool).reduce((a, b) => w.and(a, b), one)
      case 'or': return xs.map(bool).reduce((a, b) => w.or(a, b), zero)
      case 'not': return w.xor(bool(xs[0]!), one)
      case '=>': return w.or(w.xor(bool(xs[0]!), one), bool(xs[1]!))
      case '=': return pair((a, b) => w.eq(a, b))
      case 'distinct': { const v = xs.map(int); let r = one; for (let i = 0; i < v.length; i++) for (let j = i + 1; j < v.length; j++) r = w.and(r, w.ne(v[i]!, v[j]!)); return r }
      case '<': return pair(slt)
      case '<=': return pair(sle)
      case '>': return pair((a, b) => slt(b, a))
      case '>=': return pair((a, b) => sle(b, a))
      default: throw new NoWords(`the condition ${op}`)
    }
  }
  for (const [v, e] of defined) env.set(v, int(e))
  const ok = w.and(bool(guard), w.lt(point, w.source(at.count)))
  const outs: Out[] = [{wire: w.or(w.source(0), w.shl(ok, position)), write: {kind: 'register', register: 0}}]
  const stage = createWordStage({name: 'box', repeat: 'forward', circuit: w, sharedOffset: 0,
    bindings: new Map<Word, WordBinding>([[w.source(0), {kind: 'register', register: 0}], [position, {kind: 'position'}], [document, {kind: 'document'}]]), outputs: outs})
  const loop: LoopProgram<AnyStage> = {
    positions: 32, buffers: [{name: 'none', cellsPerDocument: 1}],
    registers: [{name: 'mask', initial: 0, type: 'u32'}], fields: [],
    outputGroups: [{name: 'out', kind: 'document', valuesPerDocument: 1, fill: 0, type: 'u32'}],
    stages: [stage], results: [{group: 0, column: 0, register: 0}], sharedValues: new Float32Array(cells), lengthCell: undefined,
  }
  const fill = (base: number, count: number) => { const u = new Uint32Array(loop.sharedValues.buffer); u[at.base] = base >>> 0; u[at.count] = count >>> 0; return loop.sharedValues }
  const decode = (p: number) => { const vals: number[] = []; let r = p; for (let i = 0; i < enumerated.length; i++) { vals.push((r % (2 * B + 1)) - B); r = Math.floor(r / (2 * B + 1)) } return vals }
  return {loop, fill, decode}
}
