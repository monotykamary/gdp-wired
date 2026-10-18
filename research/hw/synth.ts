// synth/'s GPU kernels (history, region, kill) as Handwired loop programs of u32 word stages (the u32-words fork), run by
// Handwired's loop runner on the CPU and by its WGSL writer (loop-emit.ts) and program runner on a GPU. They give the
// same kill sets as synth/compile.ts's hand-written kernels (check-synth.ts), behind the same Evaluator interface, so
// synth/'s Houdini, support and kernel loop run unchanged on top (run-synth.ts).
//
// Candidates are synth/'s forms Σ c·v <= d over the state and params: the coefficients (two's complement i32 bits) and
// d of candidate j sit in a shared word table at j·W.., read with `load`, and the alive bits in another. Signed
// comparison is unsigned comparison after flipping the sign bit. The kernels:
//   history  document = CHUNK histories × one block of 24 candidates. Positions walk (history, step): registers carry the
//            history's decoded params, remaining digits and state; each position checks the block's 24 candidates
//            (unrolled) against the state, and a history that ends (its last step, or a request the assumption rules
//            out) moves on to the next; `stop` after the document's last. Output: the block's kill mask.
//   region   document = 24 box points. Positions walk (point, alive candidate): a next-alive table (next[j]: the least
//            alive candidate >= j, or K) skips the dead ones, and a point stops at the first candidate it breaks.
//            Output: the 24 points' region mask.
//   kill     document = CHUNK points × one block: invariants over the list of region points (a shared table), ranks over
//            the box. Output: the block's kill mask.
import {type C, type E} from '../../core/machine.ts'
import {type AnyStage, type LoopProgram, type WordBinding, createLoopRunner, createWordStage} from '../../vendor/handwired/src/json-search/loop-program.ts'
import {emitLoopWgsl} from '../../vendor/handwired/src/json-search/loop-emit.ts'
import {type Word, WordCircuit} from '../../vendor/handwired/src/runtime/words.ts'
import {type Box, type Form, type Problem, order, points, varsOf} from '../synth/compile.ts'
import type {Evaluator} from '../synth/synth.ts'

export const BLOCK = 24
export const blocks = (K: number) => Math.ceil(K / BLOCK)
export type Kernel = 'history' | 'region' | 'kill'
export const LIST = 1 << 16 // region points per kill dispatch

type Layout = {sizes: Record<string, number>, at: Record<string, number>, sharedLength: number}

// Builds one kernel. Returns the loop program and where each shared table starts in its shared values. `cb`: candidates
// per history or kill document (24 by default; the shader unrolls them, so a smaller block compiles faster, for kernels
// whose rounds are short).
// `rankList`: a rank kill over a list of the points where the loop runs (they satisfy the guards), like an invariant kill
// over the region's points, instead of over the box.
export function compileKernel(p: Problem, box: Box, K: number, kernel: Kernel, chunk = 64, cb = BLOCK, rankList = false) {
  const listed = p.kind === 'invariant' || rankList
  const V = varsOf(p), W = V.length + 1, A = Math.ceil(K / 32)
  // History and kill read one block of 24 candidates per document: a `once` stage loads the block's coefficients and
  // alive bits into registers, so the looped stage reads registers rather than tables at every position.
  const blockRegs = kernel === 'region' ? [] : [...Array.from({length: cb}, (_, q) => Array.from({length: W}, (_, i) => `c:${q}:${i}`)).flat(), 'amask']
  const regs: string[] = [...(kernel === 'history' ? ['h', 't', 'rest', ...p.params.map(v => `p:${v}`), ...p.state.map(v => `s:${v}`), 'live', 'mask']
    : kernel === 'region' ? ['q', 'j', 'started', 'mask', ...order(p).map(v => `v:${v}`)] : ['mask']), ...blockRegs]
  const reg = (name: string) => regs.indexOf(name)
  // Shared tables after the bound cells: base, count, coefficients, alive bits, next-alive (region), list (kill, invariants).
  // One more coefficient row, of zeros, for j = K (no candidate left), so a region's reads are in range.
  const tableSizes: [string, number][] = [['base', 1], ['count', 1], ['coef', (K + 1) * W], ['alive', A]]
  if (kernel === 'region') tableSizes.push(['next', K + 1])
  if (kernel === 'kill' && listed) tableSizes.push(['list', LIST])
  const bound = regs.length + 2 // registers, then position and document
  const at: Record<string, number> = {}, sizes: Record<string, number> = {}
  let cell = bound
  for (const [name, size] of tableSizes) { at[name] = cell; sizes[name] = size; cell += size }
  const w = new WordCircuit(cell)
  const src = (name: string) => w.source(reg(name))
  const position = w.source(regs.length), document = w.source(regs.length + 1)
  const base = w.source(at.base!), count = w.source(at.count!)
  const k = (n: number) => w.constant(n >>> 0)
  const zero = k(0), one = k(1), S = k(0x80000000)
  const and = (a: Word, b: Word) => w.and(a, b), or = (a: Word, b: Word) => w.or(a, b), not = (a: Word) => w.xor(a, one)
  const sgt = (a: Word, b: Word) => w.lt(w.xor(b, S), w.xor(a, S)) // a > b as i32

  // Terms and conditions over a word environment (scalar machines and loops: no maps).
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
      case 'get': throw new Error('synthesis kernels read no maps')
    }
  }
  const cx = (c: C, env: Env): Word => {
    switch (c.op) {
      case 'all': throw new Error('the synthesizer takes no quantified flag')
      case '<': return w.lt(ex(c.a, env), ex(c.b, env))
      case '<=': return w.le(ex(c.a, env), ex(c.b, env))
      case '=': return w.eq(ex(c.a, env), ex(c.b, env))
      case 'and': return c.xs.map(y => cx(y, env)).reduce(and, one)
      case 'or': return c.xs.map(y => cx(y, env)).reduce(or, zero)
      case 'not': return not(cx(c.x, env))
      case 'flag': { const f = env.flags[c.name]; if (f === undefined) throw new Error(`unknown flag ${c.name}`); return f }
    }
  }
  const withFlags = (vars: Record<string, Word>): Env => {
    const env: Env = {vars, flags: {}}
    for (const [f, c] of Object.entries(p.flags)) env.flags[f] = cx(c, env)
    return env
  }
  const next = (env: Env): Record<string, Word> => ({...env.vars, ...Object.fromEntries(p.state.map(v => [v, ex(p.next[v]!, env)]))})
  // Candidate j's form at an environment, and its d; the alive bit.
  const coef = (j: Word, i: number) => w.load(at.coef!, sizes.coef!, w.add(w.mul(j, k(W)), k(i)))
  const form = (j: Word, vars: Record<string, Word>) => V.map((v, i) => w.mul(coef(j, i), vars[v]!)).reduce((a, b) => w.add(a, b), zero)
  const dOf = (j: Word) => coef(j, V.length)
  const alive = (j: Word) => w.and(w.shr(w.load(at.alive!, A, w.shr(j, k(5))), w.and(j, k(31))), one)
  // Over the document's block of 24 candidates (from the registers the once stage filled): bit q when candidate q is
  // alive and `bad` holds of it, given its form at an environment and its d.
  const blockForm = (q: number, vars: Record<string, Word>) => V.map((v, i) => w.mul(src(`c:${q}:${i}`), vars[v]!)).reduce((a, b) => w.add(a, b), zero)
  const overBlock = (bad: (form: (vars: Record<string, Word>) => Word, d: Word) => Word) => Array.from({length: cb}, (_, q) =>
    w.shl(and(w.and(w.shr(src('amask'), k(q)), one), bad(vars => blockForm(q, vars), src(`c:${q}:${V.length}`))), k(q))).reduce(or, zero)
  // A point's digits, lowest first: each variable within 0..box.
  const decode = (index: Word, names: string[]) => {
    const vars: Record<string, Word> = {}
    let rest = index
    for (const v of names) { vars[v] = w.mod(rest, k(box[v]! + 1)); rest = w.div(rest, k(box[v]! + 1)) }
    return {vars, rest}
  }
  const outputs: {wire: Word, write: {kind: 'register', register: number} | {kind: 'stop'}}[] = []
  let positions: number

  if (kernel === 'history') {
    const D = p.depth!, nb = Math.ceil(K / cb)
    positions = chunk * (D + 1)
    const h = src('h'), t = src('t'), fresh = w.eq(t, zero)
    const chunkIndex = w.div(document, k(nb))
    const index = w.add(base, w.add(w.mul(chunkIndex, k(chunk)), h))
    const decoded = decode(index, p.params)
    const params: Record<string, Word> = Object.fromEntries(p.params.map(v => [v, w.select(fresh, decoded.vars[v]!, src(`p:${v}`))]))
    const rest0 = w.select(fresh, decoded.rest, src('rest'))
    const preOk = p.pre ? cx(p.pre, {vars: params, flags: {}}) : one
    const live0 = w.select(fresh, and(w.lt(index, count), preOk), src('live'))
    const startVars: Record<string, Word> = {...params}
    for (const v of p.state) startVars[v] = w.select(fresh, ex(p.init![v]!, {vars: params, flags: {}}), src(`s:${v}`))
    // A step (when t > 0): this step's request, the assumption, then the state after.
    const inputs: Record<string, Word> = {}
    let rest = rest0
    for (const v of p.inputs) { inputs[v] = w.mod(rest, k(box[v]! + 1)); rest = w.div(rest, k(box[v]! + 1)) }
    const stepEnv = withFlags({...startVars, ...inputs})
    const allowed = p.assume ? cx(p.assume, stepEnv) : one
    const stepping = not(fresh)
    const live1 = w.select(stepping, and(live0, allowed), live0)
    const after = next(stepEnv)
    const state: Record<string, Word> = {...params}
    for (const v of p.state) state[v] = w.select(and(stepping, live1), after[v]!, startVars[v]!)
    const mask = or(src('mask'), w.select(live1, overBlock((f, d) => sgt(f(state), d)), zero))
    const done = or(not(live1), w.eq(t, k(D)))
    const nextH = w.select(done, w.add(h, one), h)
    outputs.push(
      {wire: w.select(done, zero, w.add(t, one)), write: {kind: 'register', register: reg('t')}},
      {wire: nextH, write: {kind: 'register', register: reg('h')}},
      {wire: w.select(stepping, rest, rest0), write: {kind: 'register', register: reg('rest')}},
      ...p.params.map(v => ({wire: params[v]!, write: {kind: 'register' as const, register: reg(`p:${v}`)}})),
      ...p.state.map(v => ({wire: state[v]!, write: {kind: 'register' as const, register: reg(`s:${v}`)}})),
      {wire: live1, write: {kind: 'register', register: reg('live')}},
      {wire: mask, write: {kind: 'register', register: reg('mask')}},
      {wire: or(w.le(k(chunk), nextH), w.le(count, w.add(base, w.add(w.mul(chunkIndex, k(chunk)), nextH)))), write: {kind: 'stop'}},
    )
  } else if (kernel === 'region') {
    positions = BLOCK * (K + 1)
    // The next-alive table's cells are candidate numbers, at most K (fill() keeps it): its reads and the coefficient
    // reads at j <= K are written without bounds checks. The point's digits are registers, counted up when it ends.
    for (let c = 0; c <= K; c++) w.assumeAtMost(w.source(at.next! + c), K)
    w.assumeAtMost(src('j'), K) // the register only ever holds a value read from that table (or its initial 0)
    const q = src('q'), started = src('started')
    const point = w.add(base, w.add(w.mul(document, k(BLOCK)), q))
    const vars: Record<string, Word> = Object.fromEntries(order(p).map(v => [v, src(`v:${v}`)]))
    const guards = [p.pre, p.assume, p.guard].filter((c): c is C => c !== undefined).map(c => cx(c, {vars, flags: {}})).reduce(and, one)
    const jcur = w.select(started, src('j'), w.load(at.next!, K + 1, zero))
    const inPoint = w.lt(point, count)
    const more = w.lt(jcur, k(K))
    const breaks = and(more, sgt(form(jcur, vars), dOf(jcur)))
    const end = or(or(not(guards), not(inPoint)), or(not(more), breaks))
    const inRegion = and(and(guards, inPoint), and(not(more), not(breaks)))
    const nextQ = w.select(end, w.add(q, one), q)
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
    const chunkIndex = w.div(document, k(nb)), j0 = w.mul(w.mod(document, k(nb)), k(cb))
    const slot = w.add(w.mul(chunkIndex, k(chunk)), position)
    let valid: Word, point: Word
    if (listed) {
      // base: the list's first entry's number; count: how many entries this dispatch's list holds.
      valid = w.lt(slot, count)
      point = w.load(at.list!, LIST, slot)
    } else {
      point = w.add(base, slot)
      valid = w.lt(point, count)
    }
    const vars = decode(point, order(p)).vars
    const guards = listed ? one : [p.pre, p.assume, p.guard].filter((c): c is C => c !== undefined).map(c => cx(c, {vars, flags: {}})).reduce(and, one)
    const env = withFlags(vars)
    const after = next(env)
    const bad = p.kind === 'invariant'
      ? (f: (vs: Record<string, Word>) => Word, d: Word) => sgt(f(after), d)
      : (f: (vs: Record<string, Word>) => Word, d: Word) => {
        // max(0, form - d), as i32, must drop.
        const r = (vs: Record<string, Word>) => { const x = w.sub(f(vs), d); return w.select(w.shr(x, k(31)), zero, x) }
        return not(w.lt(r(after), r(vars)))
      }
    void j0
    outputs.push({wire: or(src('mask'), w.select(and(valid, guards), overBlock(bad), zero)), write: {kind: 'register', register: reg('mask')}})
  }

  // The once stages: same source layout (so they share the shared values). A region document's first point's digits;
  // a history or kill document's block of candidates.
  const stages = []
  if (kernel === 'region') {
    const b = new WordCircuit(cell)
    const doc = b.source(regs.length + 1)
    let rest = b.add(b.source(at.base!), b.mul(doc, b.constant(BLOCK)))
    const outs: {wire: Word, write: {kind: 'register', register: number}}[] = []
    for (const v of order(p)) { outs.push({wire: b.mod(rest, b.constant(box[v]! + 1)), write: {kind: 'register', register: reg(`v:${v}`)}}); rest = b.div(rest, b.constant(box[v]! + 1)) }
    stages.push(createWordStage({name: 'first point', repeat: 'once', circuit: b, sharedOffset: 0, bindings: new Map<Word, WordBinding>([[doc, {kind: 'document'}]]), outputs: outs}))
  }
  if (blockRegs.length > 0) {
    const b = new WordCircuit(cell)
    const doc = b.source(regs.length + 1), j0 = b.mul(b.mod(doc, b.constant(Math.ceil(K / cb))), b.constant(cb))
    const outs: {wire: Word, write: {kind: 'register', register: number}}[] = []
    let amask = b.constant(0)
    for (let q = 0; q < cb; q++) {
      const j = b.add(j0, b.constant(q))
      for (let i = 0; i < W; i++) outs.push({wire: b.load(at.coef!, sizes.coef!, b.add(b.mul(j, b.constant(W)), b.constant(i))), write: {kind: 'register', register: reg(`c:${q}:${i}`)}})
      const bit = b.and(b.shr(b.load(at.alive!, A, b.shr(j, b.constant(5))), b.and(j, b.constant(31))), b.constant(1))
      amask = b.or(amask, b.shl(bit, b.constant(q)))
    }
    outs.push({wire: amask, write: {kind: 'register', register: reg('amask')}})
    stages.push(createWordStage({name: 'block', repeat: 'once', circuit: b, sharedOffset: 0, bindings: new Map<Word, WordBinding>([[doc, {kind: 'document'}]]), outputs: outs}))
  }
  void coef, form, dOf, alive
  const stage = createWordStage({
    name: `${kernel}`, repeat: 'forward', circuit: w, sharedOffset: 0,
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
  const layout: Layout = {sizes, at, sharedLength: cell}
  return {loop, layout, cb, work: positions! * (kernel === 'region' ? 1 : cb) * W}
}

// Fills a kernel's shared tables.
function fill(p: Problem, forms: Form[], loop: LoopProgram<AnyStage>, layout: Layout, alive: Uint32Array, base: number, count: number, list?: ArrayLike<number>) {
  const words = new Uint32Array(loop.sharedValues.buffer, loop.sharedValues.byteOffset, loop.sharedValues.length)
  const V = varsOf(p), W = V.length + 1, {at, sizes} = layout
  words[at.base!] = base >>> 0
  words[at.count!] = count >>> 0
  forms.forEach((f, j) => { V.forEach((v, i) => (words[at.coef! + j * W + i] = (f.coef[v] ?? 0) >>> 0)); words[at.coef! + j * W + V.length] = f.d >>> 0 })
  words.set(alive.subarray(0, sizes.alive!), at.alive!)
  if (at.next !== undefined) {
    const K = forms.length
    let n = K
    words[at.next + K] = K
    for (let j = K - 1; j >= 0; j--) { if ((alive[j >>> 5]! >>> (j & 31)) & 1) n = j; words[at.next + j] = n }
  }
  if (at.list !== undefined && list) { for (let i = 0; i < list.length; i++) words[at.list + i] = list[i]! }
  return loop.sharedValues
}

type Target = {kind: 'cpu'} | {kind: 'gpu', device: GPUDevice, host: any}

// One kernel on a target: run documents first..first+count-1 with the given shared values; the masks back.
async function runner(target: Target, loop: LoopProgram<AnyStage>, maxDocs: number) {
  if (target.kind === 'cpu') {
    const r = createLoopRunner(loop, 'generated')
    return {
      run: async (shared: Float32Array, docs: number) => {
        r.setShared(shared)
        const out = new Float32Array(docs), all = new Uint32Array(out.buffer), one = [new Float32Array(1)], words = new Uint32Array(one[0]!.buffer)
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

// synth/'s Evaluator, on Handwired. $SYNTH_WORK bounds a GPU dispatch's work (documents × positions × candidates checked),
// under the macOS GPU watchdog.
export async function hwEvaluator(target: Target, p: Problem, box: Box, forms: Form[], chunk = 64): Promise<Evaluator> {
  const K = forms.length, total = points(p, box)
  if (total >= 2 ** 32) throw new Error('the box has more than 2^32 points')
  const budget = Number(process.env.SYNTH_WORK ?? 4e9), maxDocs = 65535 * 64
  const docsFor = (work: number) => (target.kind === 'cpu' ? maxDocs : Math.max(64, Math.min(maxDocs, Math.floor(budget / work))))
  // A history or kill document's mask: bit q is candidate (d mod nb) × cb + q.
  const unpack = (masks: Uint32Array, killed: Set<number>, cb: number) => { const nb = Math.ceil(K / cb); masks.forEach((m, d) => { if (m) for (let q = 0; q < cb; q++) if ((m >>> q) & 1) killed.add((d % nb) * cb + q) }) }
  // The shader unrolls a block of candidates: 8 compiles 2-3× faster than 24, while 24 decodes each point a third as
  // often. A kill whose rounds are short takes 8 (an invariant kill runs over the region's few points; a rank kill when
  // points × candidates is under 10^9); history, the bulk, and a large rank kill take 24.
  const killBlock = Number(process.env.HW_KILL_BLOCK ?? (p.kind === 'rank' && total * K > 1e9 ? BLOCK : 8))
  if (p.kind === 'rank' && total > 2e6) {
    // A rank kill over a large box runs over the points where the loop runs, listed once (the guards don't depend on
    // the candidates): a straight-line word stage would otherwise pay for its block at every point the hand kernel
    // returns from early. On a small box the extra pass and shader compile cost more than they save.
    const {compileMoreKernel} = await import('./synth-more.ts')
    const g = compileMoreKernel(p, box, K, 'guards', chunk)
    const kill = compileKernel(p, box, K, 'kill', chunk, killBlock, true), nb = Math.ceil(K / kill.cb)
    const guardDocs = docsFor(BLOCK * 8), killChunks = Math.max(1, Math.min(Math.ceil(LIST / chunk), Math.floor(docsFor(kill.work) / nb)))
    const [gr, kr] = await Promise.all([runner(target, g.loop, guardDocs), runner(target, kill.loop, killChunks * nb)])
    const guarded: number[] = []
    const gwords = new Uint32Array(g.loop.sharedValues.buffer)
    for (let first = 0; first < total; first += guardDocs * BLOCK) {
      gwords[g.layout.at.base!] = first; gwords[g.layout.at.count!] = total
      const docs = Math.min(guardDocs, Math.ceil((total - first) / BLOCK))
      const masks = await gr.run(g.loop.sharedValues, docs)
      masks.forEach((m, d) => { if (m) for (let q = 0; q < BLOCK; q++) if ((m >>> q) & 1) guarded.push(first + d * BLOCK + q) })
    }
    gr.destroy()
    return {
      name: `handwired words (${target.kind})`,
      round: async alive => {
        const killed = new Set<number>()
        for (let from = 0; from < guarded.length; from += LIST) {
          const list = guarded.slice(from, from + LIST)
          for (let c = 0; c * chunk < list.length; c += killChunks) {
            const sub = list.slice(c * chunk, (c + killChunks) * chunk)
            unpack(await kr.run(fill(p, forms, kill.loop, kill.layout, alive, 0, sub.length, sub), Math.ceil(sub.length / chunk) * nb), killed, kill.cb)
          }
        }
        return [...killed]
      },
      destroy: kr.destroy,
    }
  }
  if (p.kind !== 'invariant') {
    // history, or a rank kill over a small box: documents = chunks × blocks over the space.
    const kernel = p.kind === 'history' ? 'history' : 'kill'
    const {loop, layout, work, cb} = compileKernel(p, box, K, kernel, chunk, kernel === 'kill' ? killBlock : BLOCK)
    const nb = Math.ceil(K / cb)
    const chunksPer = Math.max(1, Math.floor(docsFor(work) / nb))
    const r = await runner(target, loop, chunksPer * nb)
    return {
      name: `handwired words (${target.kind})`,
      round: async alive => {
        const killed = new Set<number>()
        for (let first = 0; first < total; first += chunksPer * chunk) {
          const docs = Math.min(chunksPer, Math.ceil((total - first) / chunk)) * nb
          unpack(await r.run(fill(p, forms, loop, layout, alive, first, total), docs), killed, cb)
        }
        return [...killed]
      },
      destroy: r.destroy,
    }
  }
  const region = compileKernel(p, box, K, 'region', chunk), kill = compileKernel(p, box, K, 'kill', chunk, killBlock), nb = Math.ceil(K / kill.cb)
  // Most points stop within a candidate or two: a region dispatch is sized for about 2 positions a point, so there are
  // few large dispatches (each costs a sync, an upload and a readback).
  const regionDocs = docsFor(BLOCK * 2 * (varsOf(p).length + 1))
  const killChunks = Math.max(1, Math.min(Math.ceil(LIST / chunk), Math.floor(docsFor(kill.work) / nb)))
  // Created together, so the two shader compiles overlap.
  const [rr, kr] = await Promise.all([runner(target, region.loop, regionDocs), runner(target, kill.loop, killChunks * nb)])
  return {
    name: `handwired words (${target.kind})`,
    round: async alive => {
      const inRegion: number[] = []
      for (let first = 0; first < total; first += regionDocs * BLOCK) {
        const docs = Math.min(regionDocs, Math.ceil((total - first) / BLOCK))
        const masks = await rr.run(fill(p, forms, region.loop, region.layout, alive, first, total), docs)
        masks.forEach((m, d) => { if (m) for (let q = 0; q < BLOCK; q++) if ((m >>> q) & 1) inRegion.push(first + d * BLOCK + q) })
      }
      const killed = new Set<number>()
      for (let from = 0; from < inRegion.length; from += LIST) {
        const list = inRegion.slice(from, from + LIST)
        for (let c = 0; c * chunk < list.length; c += killChunks) {
          const sub = list.slice(c * chunk, (c + killChunks) * chunk)
          const docs = Math.ceil(sub.length / chunk) * nb
          unpack(await kr.run(fill(p, forms, kill.loop, kill.layout, alive, 0, sub.length, sub), docs), killed, kill.cb)
        }
      }
      lastRegion = inRegion.length
      return [...killed]
    },
    destroy: () => { rr.destroy(); kr.destroy() },
  }
}
export let lastRegion = 0
