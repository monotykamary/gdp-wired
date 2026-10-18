// The predicate enumeration (enum/) as a Handwired loop program of u32 word stages, generated from the laws instead of
// enum/kernel-page.ts's hand-written shader. A world is k atoms, the bits of a word w = (document << 11) | position, so a
// document is a block of 2,048 worlds and the stage counts, per block, the reachable worlds and the violations.
//
// Laws are formulas over atoms, written per atom index i over an index set: e.g. "for every even i, not (a[i+1] and not
// a[i])". `lanes` compiles such a formula to word operations: atom a[i+c] is w >> c (bit i of it is a[i+c]), and, or
// and not work on every lane at once, and the index set is a mask. `any`/`none` of a family is (word & mask) != 0 / == 0.
// So a family of k/2 clauses costs a handful of word operations, whatever k.
import {type AnyStage, type LoopProgram, createWordStage} from '../../vendor/handwired/src/json-search/loop-program.ts'
import {type Word, WordCircuit} from '../../vendor/handwired/src/runtime/words.ts'

// A formula over the atoms at offsets from a lane's index i, or a single atom.
export type F =
  | {op: 'atom', offset: number} // a[i + offset]
  | {op: 'and' | 'or', xs: F[]}
  | {op: 'not', x: F}
// A boolean of the world: a family's any/none over an index set, a single atom, and connectives.
export type B =
  | {op: 'any' | 'none', family: F, lanes: number[]}
  | {op: 'bit', atom: number}
  | {op: 'and' | 'or', xs: B[]}
  | {op: 'not', x: B}

export const atom = (offset: number): F => ({op: 'atom', offset})
export const fand = (...xs: F[]): F => ({op: 'and', xs}), fnot = (x: F): F => ({op: 'not', x})

// enum/'s laws for k atoms (template.bend, circuit.ts): reachable (no odd atom without the even atom below it); the
// policy (some clause a[i] a[i+1] !a[i+2], for i = 0, 3, 6, ...); the proposal (the same, but clause 0 also needs the
// top atom); a violation is a reachable world the policy allows and the proposal doesn't.
export function laws(k: number) {
  const evens = Array.from({length: k}, (_, i) => i).filter(i => i % 2 === 0 && i + 1 < k)
  const starts = Array.from({length: k}, (_, i) => i).filter(i => i % 3 === 0 && i + 2 < k)
  const clause = fand(atom(0), atom(1), fnot(atom(2)))
  const reachable: B = {op: 'none', family: fand(atom(1), fnot(atom(0))), lanes: evens}
  const policy: B = {op: 'any', family: clause, lanes: starts}
  const proposal: B = {op: 'or', xs: [{op: 'and', xs: [{op: 'any', family: clause, lanes: [0]}, {op: 'bit', atom: k - 1}]}, {op: 'any', family: clause, lanes: starts.slice(1)}]}
  const violation: B = {op: 'and', xs: [reachable, policy, {op: 'not', x: proposal}]}
  return {reachable, violation}
}

// The same laws evaluated atom by atom, the reference for `lanes`.
export function evaluate(b: B, world: number): boolean {
  const a = (i: number) => ((world >>> i) & 1) === 1
  const f = (x: F, i: number): boolean => x.op === 'atom' ? a(i + x.offset) : x.op === 'not' ? !f(x.x, i) : x.op === 'and' ? x.xs.every(y => f(y, i)) : x.xs.some(y => f(y, i))
  switch (b.op) {
    case 'any': return b.lanes.some(i => f(b.family, i))
    case 'none': return !b.lanes.some(i => f(b.family, i))
    case 'bit': return a(b.atom)
    case 'and': return b.xs.every(y => evaluate(y, world))
    case 'or': return b.xs.some(y => evaluate(y, world))
    case 'not': return !evaluate(b.x, world)
  }
}

// Compiles a boolean of the world to a word that is 1 or 0.
export function lanes(c: WordCircuit, w: Word, b: B): Word {
  const k = (n: number) => c.constant(n >>> 0), one = k(1), zero = k(0)
  const family = (x: F): Word => x.op === 'atom' ? (x.offset === 0 ? w : c.shr(w, k(x.offset))) : x.op === 'not' ? c.not(family(x.x))
    : x.xs.map(family).reduce((p, q) => (x.op === 'and' ? c.and(p, q) : c.or(p, q)))
  const mask = (lanesOf: number[]) => lanesOf.reduce((m, i) => (m | (1 << i)) >>> 0, 0)
  switch (b.op) {
    case 'any': return b.lanes.length === 0 ? zero : c.ne(c.and(family(b.family), k(mask(b.lanes))), zero)
    case 'none': return b.lanes.length === 0 ? one : c.eq(c.and(family(b.family), k(mask(b.lanes))), zero)
    case 'bit': return c.and(c.shr(w, k(b.atom)), one)
    case 'and': return b.xs.map(x => lanes(c, w, x)).reduce((p, q) => c.and(p, q))
    case 'or': return b.xs.map(x => lanes(c, w, x)).reduce((p, q) => c.or(p, q))
    case 'not': return c.xor(lanes(c, w, b.x), one)
  }
}

// A last stage that packs two counters, each below 4096, into one output word (high << 12 | low), so a document reads
// back one u32, as the hand-written shaders' one f32 each.
export function packStage(high: number, low: number, sharedOffset: number) {
  const c = new WordCircuit(2)
  return createWordStage({name: 'pack', repeat: 'once', circuit: c, sharedOffset,
    bindings: new Map([[c.source(0), {kind: 'register' as const, register: high}], [c.source(1), {kind: 'register' as const, register: low}]]),
    outputs: [{wire: c.or(c.shl(c.source(0), c.constant(12)), c.source(1)), write: {kind: 'document', group: 0, column: 0}}]})
}

export const LOW = 11
// pack: one output word per block, reachable << 12 | violations (both at most 2,048), instead of two.
export function buildEnum(k: number, pack = false): {loop: LoopProgram<AnyStage>, documents: number} {
  const {reachable, violation} = laws(k)
  // Sources: the two counters (registers), the document and the position.
  const c = new WordCircuit(4)
  const [r, v, doc, pos] = [0, 1, 2, 3].map(i => c.source(i)) as [Word, Word, Word, Word]
  const w = c.or(c.shl(doc, c.constant(LOW)), pos)
  const stage = createWordStage({
    name: `enumerate ${k}`, repeat: 'forward', circuit: c, sharedOffset: 0,
    bindings: new Map([[r, {kind: 'register', register: 0}], [v, {kind: 'register', register: 1}], [doc, {kind: 'document'}], [pos, {kind: 'position'}]]),
    outputs: [
      {wire: c.add(r, lanes(c, w, reachable)), write: {kind: 'register', register: 0}},
      {wire: c.add(v, lanes(c, w, violation)), write: {kind: 'register', register: 1}},
    ],
  })
  const loop: LoopProgram<AnyStage> = {
    positions: 1 << LOW, buffers: [{name: 'none', cellsPerDocument: 1}],
    registers: [{name: 'reachable', initial: 0, type: 'u32'}, {name: 'violations', initial: 0, type: 'u32'}], fields: [],
    outputGroups: [{name: 'counts', kind: 'document', valuesPerDocument: pack ? 1 : 2, fill: 0, type: 'u32'}],
    stages: pack ? [stage, packStage(0, 1, 4)] : [stage], results: pack ? [] : [{group: 0, column: 0, register: 0}, {group: 0, column: 1, register: 1}],
    sharedValues: new Float32Array(pack ? 6 : 4), lengthCell: undefined,
  }
  return {loop, documents: 2 ** (k - LOW)}
}
