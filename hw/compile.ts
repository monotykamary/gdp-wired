// A machine and a law as a Handwired loop program of u32 word stages (the u32-words fork: src/runtime/words.ts), so the
// counterexample search runs through Handwired itself: its loop runner on the CPU, its WGSL writer (loop-emit.ts) and
// its GPU program runner. This replaces search/compile.ts's hand-written shader.
//
// One document covers `chunk` consecutive candidates (params, then each step's request, as digits in base bound + 1, as
// in search/). The looped stage runs at most chunk × depth positions, a step of one candidate each: registers t and off
// say which step of which candidate, and when a candidate is done (it failed, a request wasn't allowed, or its last
// step passed) the next position starts the next one, and the stage stops (the fork's `stop` write) after the last.
// At step 0 it decodes the candidate from base + document × chunk + offset (base is a shared word, so 2^32
// candidates fit), starts the machine, and checks the law at the start; then it takes the step and checks the law
// after it. Registers carry the candidate's state, its remaining digits, and the best failure so far, kept as
// depth × chunk + offset (0xffffffff: none), the least over the document's candidates, its only output. A `once` stage
// first works out the document's first candidate and how many it has.
//
// Maps: cells 0..bound are registers, a read past them is the map's initial value, and a step writes only at a param or
// input key, as in search/. A law with `forall` is checked at every cell and at key bound + 1.
//
// A step law over k steps (kernel.ts's StepLaw, read on a run as core/watch.ts reads it) is checked after every step that
// ends k steps in a row: registers hold the last k − 1 steps' frames (the state and cells before each, and its request),
// shifted on at every step; each step's `when` is read at its own frame, `then` across the window (plain names at the
// first frame, input@j the j-th request, primed names after this step). A candidate's params must meet `pre`.
//
// A machine with a history steps as kernel.ts's plain machine (its sums are state), and a candidate's digits are the
// requests' carried inputs only: registers hold the log (each step's recorded inputs, and whether it was kept), and each
// query is the sum of its term over the records kept before the request and not yet spent (with pruning, a record whose
// order plus `after` is at most the request's), as the runtimes read it. With pruning, a request whose order goes back
// ends the candidate: the runtimes refuse it.
import {type C, type E, type Machine} from '../core/machine.ts'
import {carried, fitsU32, stepDigits} from '../search/compile.ts'
import {historyMachine} from '../kernel/kernel.ts'
import {type Watched, isStepLaw} from '../core/watch.ts'
import {type AnyStage, type LoopProgram, type WordBinding, createWordStage} from '../vendor/handwired/src/json-search/loop-program.ts'
import {type Word, WordCircuit} from '../vendor/handwired/src/runtime/words.ts'

export type Space = {depth: number, bound: number}

// Spaces past 2^32 candidates run in slices: the index's digits cover the params and the first `low` steps, and the
// requests of the later steps come from the shared word `hi`, one number per slice (low = depth: no slices).
// `at most`: fewer low steps than fit, to test slicing on a small space.
export function lowSteps(m: Machine, space: Space, atMost = space.depth) {
  const K = space.bound + 1
  let low = Math.min(space.depth, atMost)
  while (low > 0 && K ** (m.params.length + stepDigits(m, space.bound) * low) > 2 ** 32 - 1) low--
  return low
}

export function compile(given: Machine, law: Watched, space: Space, chunk: number, lowAtMost = space.depth): LoopProgram<AnyStage> {
  const K = space.bound + 1, D = space.depth, L = lowSteps(given, space, lowAtMost)
  fitsU32(given, law, space)
  const h = given.history, m = h ? historyMachine(given).machine : given, carriedIn = carried(given)
  const log = h ? Array.from({length: D}, (_, i) => [...h.record.map(f => `r${i}:${f}`), `k${i}`]).flat() : []
  const steps = isStepLaw(law) ? law.steps ?? 1 : 0
  if (steps > D) throw new Error(`${law.name}: a law over ${steps} steps needs a depth of at least ${steps}`)
  const isVar = (e: E) => e.op === 'var' && (m.params.includes(e.name) || m.inputs.includes(e.name))
  for (const w of Object.values(m.step.maps ?? {})) if (!('each' in w) && !isVar(w.key)) throw new Error('a step writes maps only at a param or input key, or at every key')
  const maps = Object.keys(m.maps ?? {}), carriedMaps = m.inputMaps ?? []
  const state = Object.keys(m.state)
  // A map written at every key keeps its default (what every cell past 0..bound reads) in a register; any other reads
  // its initial value there.
  const kept = maps.filter(map => { const w = m.step.maps?.[map]; return w !== undefined && 'each' in w })
  // Registers: the remaining digits, params, state, map cells, the candidate's flags, and the best failure.
  // A step law's window: the j-th earlier step's frame (j = 1 the step before this one), its state, cells and request.
  const slot = (j: number) => [...state.map(s => `w${j}:s:${s}`), ...maps.flatMap(map => Array.from({length: K}, (_, c) => `w${j}:m:${map}:${c}`)), ...kept.map(map => `w${j}:d:${map}`),
    ...carriedMaps.flatMap(map => Array.from({length: K}, (_, c) => `w${j}:c:${map}:${c}`)), ...m.inputs.map(i => `w${j}:i:${i}`)]
  const slots = Array.from({length: Math.max(0, steps - 1)}, (_, j) => slot(j + 1)).flat()
  const regs: string[] = ['t', 'off', 'rest', ...m.params.map(p => `p:${p}`), ...state.map(s => `s:${s}`), ...maps.flatMap(map => Array.from({length: K}, (_, c) => `m:${map}:${c}`)), ...kept.map(map => `d:${map}`), ...slots, ...log, ...(h?.prune ? ['last'] : []), 'live', 'best', 'first', 'count']
  const reg = (name: string) => { const r = regs.indexOf(name); if (r < 0) throw new Error(name); return r }

  // Source cells: one per register, then the position, the document, and three shared words: hi, base and total.
  const w = new WordCircuit(regs.length + 5)
  const src = (name: string) => w.source(reg(name))
  // What the registers can hold, so the circuit folds what follows from it (contracts the executor checks).
  w.assumeAtMost(src('live'), 1)
  w.assumeAtMost(src('t'), D - 1)
  w.assumeAtMost(src('off'), chunk)
  w.assumeAtMost(src('count'), chunk)
  for (const p of m.params) w.assumeAtMost(src(`p:${p}`), K - 1)
  const position = w.source(regs.length), document = w.source(regs.length + 1), hi = w.source(regs.length + 2), _base = w.source(regs.length + 3), total = w.source(regs.length + 4)
  const k = (n: number) => w.constant(n >>> 0)
  const one = k(1), zero = k(0)
  const not = (a: Word) => w.xor(a, one), and = (a: Word, b: Word) => w.and(a, b), or = (a: Word, b: Word) => w.or(a, b)

  // The step within the candidate and the candidate's offset, carried in registers rather than divided out of the
  // position each time: t counts 0..depth-1, and off moves on when t wraps.
  const t = src('t'), off = src('off'), fresh = w.eq(t, zero)
  void position
  // At step 0: the candidate's index, its params (the lowest digits) and the start.
  // The document's first candidate and how many it has are worked out once, by the `once` stage below.
  const index = w.add(src('first'), off)
  let digits = index
  const params: Record<string, Word> = {}
  for (const p of m.params) { const d = w.mod(digits, k(K)); digits = w.div(digits, k(K)); params[p] = w.select(fresh, d, src(`p:${p}`)) }
  const rest0 = w.select(fresh, digits, src('rest'))
  void total

  // Terms over an environment of words; map reads go through `cells` (0..bound) and `defaults` (past them). A key bound
  // by a quantified flag or a write at every key is read only as a map's key: at one cell, or past them all.
  type Env = {vars: Record<string, Word>, cells: Record<string, Word[]>, flags: Record<string, Word>, defaults?: Record<string, Word>, bound?: {name: string, cell: number | 'past'}}
  const fallback = (map: string, env: Env): Word => env.defaults?.[map] ?? (carriedMaps.includes(map.replace(/(@\d+|')$/, '')) ? zero : k(m.maps![map.replace(/'$/, '')]!)) // M' starts as M
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
      case 'get': {
        const cells = env.cells[e.map]!
        if (env.bound && e.key.op === 'var' && e.key.name === env.bound.name) return env.bound.cell === 'past' ? fallback(e.map, env) : cells[env.bound.cell]!
        const key = ex(e.key, env)
        // The cell at the key, or the map's initial value past the stored cells; a key that can't be past them starts
        // the chain from the last cell.
        if (w.maximum(key) < cells.length) return cells.slice(0, -1).reduce((acc, cell, c) => w.select(w.eq(key, k(c)), cell, acc), cells.at(-1)!)
        return cells.reduce((acc, cell, c) => w.select(w.eq(key, k(c)), cell, acc), fallback(e.map, env))
      }
    }
  }
  const cx = (c: C, env: Env): Word => {
    switch (c.op) {
      // Every cell 0..bound, and past them (where every map reads its default).
      case 'all': return [...Array.from({length: K}, (_, cell) => cell), 'past' as const].map(cell => cx(c.c, {...env, bound: {name: c.key, cell}})).reduce(and, one)
      case '<': return w.lt(ex(c.a, env), ex(c.b, env))
      case '<=': return w.le(ex(c.a, env), ex(c.b, env))
      case '=': return w.eq(ex(c.a, env), ex(c.b, env))
      case 'and': return c.xs.map(y => cx(y, env)).reduce(and, one)
      case 'or': return c.xs.map(y => cx(y, env)).reduce(or, zero)
      case 'not': return not(cx(c.x, env))
      case 'flag': { const f = env.flags[c.name]; if (f === undefined) throw new Error(`unknown flag ${c.name}`); return f }
    }
  }
  // A condition at every key (0..bound + 1) for a law about every key, or once.
  const atKeys = (c: C, env: Env, forall: string | undefined): Word => forall
    ? Array.from({length: K + 1}, (_, key) => cx(c, {...env, vars: {...env.vars, [forall]: k(key)}})).reduce(and, one)
    : cx(c, env)
  const holds = (env: Env): Word => (isStepLaw(law) ? one : atKeys(law.holds, env, law.forall))

  // The start, from the params; the registers' state otherwise.
  const startEnv: Env = {vars: {...params}, cells: {}, flags: {}}
  // A document past the space's end has no candidate, and neither do params that miss the precondition.
  const live0 = w.select(fresh, m.pre ? and(w.lt(off, src('count')), cx(m.pre, startEnv)) : w.lt(off, src('count')), src('live'))
  const vars0: Record<string, Word> = {...params}
  for (const s of state) vars0[s] = w.select(fresh, ex(m.state[s]!, startEnv), src(`s:${s}`))
  const cells0: Record<string, Word[]> = Object.fromEntries(maps.map(map => [map, Array.from({length: K}, (_, c) => w.select(fresh, k(m.maps![map]!), src(`m:${map}:${c}`)))]))
  const defaults0: Record<string, Word> = Object.fromEntries(kept.map(map => [map, w.select(fresh, k(m.maps![map]!), src(`d:${map}`))]))
  const before: Env = {vars: vars0, cells: cells0, flags: {}, defaults: defaults0}
  const best0 = src('best')
  // The best failure is depth × chunk + offset, and 0xffffffff while there is none, so the least is a plain min.
  const record = (failed: Word, depth: Word, current: Word) => w.select(failed, w.min(current, w.add(w.mul(depth, k(chunk)), off)), current)
  // The law at the start, checked at step 0 of a live candidate, on the start itself (the params' initial state, every
  // map cell its constant initial value), so most of it folds to constants instead of being evaluated every position.
  const initVars: Record<string, Word> = {...params}
  for (const st of state) initVars[st] = ex(m.state[st]!, startEnv)
  const initEnv: Env = {vars: initVars, cells: Object.fromEntries(maps.map(map => [map, Array.from({length: K}, () => k(m.maps![map]!))])), flags: {}}
  const startFails = isStepLaw(law) ? zero : and(and(fresh, live0), not(holds(initEnv)))
  const bestStart = record(startFails, zero, best0)
  const live1 = and(live0, not(startFails))

  // The step: this step's request, the assumption, flags, then the state after.
  const inputs: Record<string, Word> = {}
  // At step `low` the index's digits are used up, and the slice's number holds the rest.
  let rest = L < D ? w.select(w.eq(t, k(L)), hi, rest0) : rest0
  for (const i of carriedIn) { inputs[i] = w.mod(rest, k(K)); rest = w.div(rest, k(K)) }
  // Each map the request carries: a digit per cell, 0 past them.
  const carriedCells: Record<string, Word[]> = {}
  for (const map of carriedMaps) carriedCells[map] = Array.from({length: K}, () => { const d = w.mod(rest, k(K)); rest = w.div(rest, k(K)); return d })
  // The queries, from the log: each record kept at an earlier step of this candidate and not yet spent.
  const order = h?.prune ? inputs[h.prune.order]! : undefined
  if (h) {
    const after = h.prune ? ex(h.prune.after, {vars: {...params}, cells: {}, flags: {}}) : undefined
    const records = Array.from({length: D}, (_, i) => {
      const fields = Object.fromEntries(h.record.map(f => [`r.${f}`, src(`r${i}:${f}`)]))
      const counts = and(w.lt(k(i), t), src(`k${i}`))
      return {fields, counts: after ? and(counts, w.lt(order!, w.add(src(`r${i}:${h.prune!.order}`), after))) : counts}
    })
    for (const [q, g] of Object.entries(h.queries)) {
      inputs[q] = records.reduce((acc, r) => w.add(acc, w.select(r.counts, ex(g, {vars: {...params, ...inputs, ...r.fields}, cells: {}, flags: {}}), zero)), zero)
    }
  }
  const stepEnv: Env = {vars: {...before.vars, ...inputs}, cells: {...before.cells, ...carriedCells}, flags: {}, defaults: before.defaults}
  for (const [f, c] of Object.entries(m.step.flags ?? {})) stepEnv.flags[f] = cx(c, stepEnv)
  // The machine's own assumption (as the runtimes check it, without the relations the kernel proves of the log); with
  // pruning, a request in order.
  const assumed = given.assume ? cx(given.assume, stepEnv) : one
  const allowed = order ? and(assumed, or(fresh, w.le(src('last'), order))) : assumed
  const go = and(live1, allowed)
  const vars1: Record<string, Word> = {...params}
  for (const s of state) vars1[s] = m.step.state?.[s] ? w.select(go, ex(m.step.state[s]!, stepEnv), before.vars[s]!) : before.vars[s]!
  const cells1: Record<string, Word[]> = {}, defaults1: Record<string, Word> = {...before.defaults}
  for (const map of maps) {
    const write = m.step.maps?.[map]
    if (write && 'each' in write) {
      cells1[map] = before.cells[map]!.map((cell, c) => w.select(go, ex(write.value, {...stepEnv, bound: {name: write.each, cell: c}}), cell))
      defaults1[map] = w.select(go, ex(write.value, {...stepEnv, bound: {name: write.each, cell: 'past'}}), before.defaults![map]!)
      continue
    }
    cells1[map] = before.cells[map]!.map((cell, c) => {
      if (!write) return cell
      const key = ex(write.key, stepEnv), value = ex(write.value, stepEnv)
      return w.select(and(go, w.eq(key, k(c))), value, cell)
    })
  }
  const after: Env = {vars: vars1, cells: cells1, flags: {}, defaults: defaults1}
  let stepFails = and(go, not(holds(after)))
  if (isStepLaw(law)) {
    // The window's frames, oldest first: the k − 1 earlier steps' from their slots, then this one.
    const frame = (j: number): Env => {
      if (j === 0) return stepEnv
      const vars: Record<string, Word> = {...params}
      for (const s of state) vars[s] = src(`w${j}:s:${s}`)
      for (const i of m.inputs) vars[i] = src(`w${j}:i:${i}`)
      const env: Env = {vars, cells: Object.fromEntries([...maps.map(map => [map, Array.from({length: K}, (_, c) => src(`w${j}:m:${map}:${c}`))]),
        ...carriedMaps.map(map => [map, Array.from({length: K}, (_, c) => src(`w${j}:c:${map}:${c}`))])]), flags: {}, defaults: Object.fromEntries(kept.map(map => [map, src(`w${j}:d:${map}`)]))}
      for (const [f, c] of Object.entries(m.step.flags ?? {})) env.flags[f] = cx(c, env)
      return env
    }
    const frames = Array.from({length: steps}, (_, j) => frame(steps - 1 - j))
    const whens = law.when === undefined ? [] : Array.isArray(law.when) ? law.when : [law.when]
    const meets = whens.map((c, j) => cx(c, frames[j]!)).reduce(and, one)
    // `then`: the first frame by plain names (its request and flags too), the j-th request as input@j, and after this
    // step by primed names.
    const first = frames[0]!
    const thenVars: Record<string, Word> = {...first.vars}
    frames.slice(1).forEach((f, j) => { for (const i of m.inputs) thenVars[`${i}@${j + 2}`] = f.vars[i]! })
    for (const s of state) thenVars[`${s}'`] = vars1[s]!
    const across: Env = {vars: thenVars, flags: first.flags,
      cells: {...first.cells, ...Object.fromEntries(maps.map(map => [`${map}'`, cells1[map]!])), ...Object.fromEntries(frames.slice(1).flatMap((f, j) => carriedMaps.map(map => [`${map}@${j + 2}`, f.cells[map]!])))},
      defaults: {...first.defaults, ...Object.fromEntries(kept.map(map => [`${map}'`, defaults1[map]!]))}}
    // A full window: this is at least the k-th step of the candidate (every earlier one was allowed, or it had ended).
    const full = steps === 1 ? one : w.le(k(steps - 1), t)
    stepFails = and(and(go, full), and(meets, not(atKeys(law.then, across, law.forall))))
  }
  const best1 = record(stepFails, w.add(t, one), bestStart)
  const bestOut = best1

  // The candidate is done when it failed, a request wasn't allowed, or its last step passed: the next position starts
  // the next candidate, and the loop stops when the document's candidates (or all of them) are done. So a candidate
  // costs only the steps it lives, as with the early returns of search/'s shader.
  const liveAfter = and(go, not(stepFails))
  const done = or(not(liveAfter), w.eq(t, k(D - 1)))
  const nextOff = w.select(done, w.add(off, one), off)
  const finished = w.le(src('count'), nextOff)
  const outputs: {wire: Word, write: {kind: 'register', register: number} | {kind: 'stop'}}[] = [
    {wire: w.select(done, zero, w.add(t, one)), write: {kind: 'register', register: reg('t')}},
    {wire: nextOff, write: {kind: 'register', register: reg('off')}},
    {wire: finished, write: {kind: 'stop'}},
    {wire: rest, write: {kind: 'register', register: reg('rest')}},
    ...m.params.map(p => ({wire: params[p]!, write: {kind: 'register' as const, register: reg(`p:${p}`)}})),
    ...state.map(s => ({wire: vars1[s]!, write: {kind: 'register' as const, register: reg(`s:${s}`)}})),
    ...maps.flatMap(map => cells1[map]!.map((cell, c) => ({wire: cell, write: {kind: 'register' as const, register: reg(`m:${map}:${c}`)}}))),
    ...kept.map(map => ({wire: defaults1[map]!, write: {kind: 'register' as const, register: reg(`d:${map}`)}})),
    // A candidate that failed or whose request isn't allowed stops: nothing later counts.
    // The window moves on: this step's frame into slot 1, each slot into the next.
    ...Array.from({length: Math.max(0, steps - 1)}, (_, j) => j + 1).flatMap(j => [
      ...state.map(s => ({wire: j === 1 ? before.vars[s]! : src(`w${j - 1}:s:${s}`), write: {kind: 'register' as const, register: reg(`w${j}:s:${s}`)}})),
      ...maps.flatMap(map => Array.from({length: K}, (_, c) => ({wire: j === 1 ? before.cells[map]![c]! : src(`w${j - 1}:m:${map}:${c}`), write: {kind: 'register' as const, register: reg(`w${j}:m:${map}:${c}`)}}))),
      ...kept.map(map => ({wire: j === 1 ? before.defaults![map]! : src(`w${j - 1}:d:${map}`), write: {kind: 'register' as const, register: reg(`w${j}:d:${map}`)}})),
      ...carriedMaps.flatMap(map => Array.from({length: K}, (_, c) => ({wire: j === 1 ? carriedCells[map]![c]! : src(`w${j - 1}:c:${map}:${c}`), write: {kind: 'register' as const, register: reg(`w${j}:c:${map}:${c}`)}}))),
      ...m.inputs.map(i => ({wire: j === 1 ? inputs[i]! : src(`w${j - 1}:i:${i}`), write: {kind: 'register' as const, register: reg(`w${j}:i:${i}`)}})),
    ]),
    // The log: this step's record, kept if the step was taken and keeps it; the last order.
    ...(h ? Array.from({length: D}, (_, i) => [
      ...h.record.map(f => ({wire: w.select(w.eq(t, k(i)), inputs[f]!, src(`r${i}:${f}`)), write: {kind: 'register' as const, register: reg(`r${i}:${f}`)}})),
      {wire: w.select(w.eq(t, k(i)), and(go, cx(h.keep, stepEnv)), src(`k${i}`)), write: {kind: 'register' as const, register: reg(`k${i}`)}},
    ]).flat() : []),
    ...(order ? [{wire: w.select(go, order, src('last')), write: {kind: 'register' as const, register: reg('last')}}] : []),
    {wire: liveAfter, write: {kind: 'register', register: reg('live')}},
    {wire: bestOut, write: {kind: 'register', register: reg('best')}},
  ]
  // Once per document: its first candidate, and how many it has (fewer than chunk at the end of the space).
  const o = new WordCircuit(4)
  const [oDoc, oBase, oTotal] = [o.source(0), o.source(1), o.source(2)]
  const first = o.add(oBase, o.mul(oDoc, o.constant(chunk)))
  const count = o.min(o.constant(chunk), o.monus(oTotal, first))
  const start = createWordStage({name: 'documents', repeat: 'once', circuit: o, sharedOffset: w.sourceSize,
    bindings: new Map<Word, WordBinding>([[oDoc, {kind: 'document'}], [o.source(3), {kind: 'register', register: reg('best')}]]),
    outputs: [{wire: first, write: {kind: 'register', register: reg('first')}}, {wire: count, write: {kind: 'register', register: reg('count')}},
      {wire: o.constant(0xffffffff), write: {kind: 'register', register: reg('best')}}]})
  const stage = createWordStage({
    name: `${m.name}: ${law.name}`, repeat: 'forward', circuit: w, sharedOffset: 0,
    bindings: new Map<Word, WordBinding>([
      ...regs.map((name, r) => [w.source(r), {kind: 'register' as const, register: r}] as const),
      [position, {kind: 'position'}], [document, {kind: 'document'}],
    ]),
    outputs,
  })
  // Shared words: each stage's source table; the looped stage reads hi, and the once stage base and total.
  const shared = new Float32Array(w.sourceSize + 4)
  return {
    positions: chunk * D, buffers: [{name: 'none', cellsPerDocument: 1}],
    registers: regs.map(name => ({name, initial: 0, type: 'u32' as const})), fields: [],
    outputGroups: [{name: 'best', kind: 'document', valuesPerDocument: 1, fill: 0, type: 'u32'}],
    stages: [start, stage], results: [{group: 0, column: 0, register: reg('best')}], sharedValues: shared, lengthCell: undefined,
  }
}

// The shared words of a dispatch: the slice, where its candidates start within the slice, and how many it holds. The
// looped stage's table ends with hi, base, total (cells n − 3..n − 1); the once stage's (after it) holds base, total at
// cells 1, 2.
export function setRange(loop: LoopProgram<AnyStage>, base: number, total: number, hi = 0) {
  const words = new Uint32Array(loop.sharedValues.buffer, loop.sharedValues.byteOffset, loop.sharedValues.length)
  const n = words.length - 4
  words[n - 3] = hi >>> 0
  words[n - 2] = base >>> 0
  words[n - 1] = total >>> 0
  words[n + 1] = base >>> 0
  words[n + 2] = total >>> 0
  return loop.sharedValues
}

// A document's output: the least failing (depth, candidate index), or undefined.
export function decodeBest(value: number, base: number, document: number, chunk: number) {
  if (value === 0xffffffff) return undefined
  return {depth: Math.floor(value / chunk), index: base + document * chunk + (value % chunk)}
}
