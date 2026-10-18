// The ReBAC audit (next/rebac) as a Handwired loop program of u32 word stages, in place of next/rebac/page.ts's
// hand-written shader. A document is a user, whose cells (Handwired's per-document store) are its groups as two 16-bit
// halves and its two direct grants as object + 1 (0: none), all whole numbers an f32 cell holds exactly. The object
// side is shared words: each object's inherited groups, Euler interval and whether it lies under /finance, and each
// group's nesting.
//   stage 'closure' (once):  the user's groups closed under nesting, the grants' intervals, and whether the user is in
//                            Finance. model.ts's closure is 5 rounds of R(G) = G ∪ ⋃_{g∈G} sub[g]; R distributes over
//                            union, so R^5(G) = ⋃_{g∈G} R^5({g}) exactly, and with R^5({g}) a shared table (star) it
//                            is one round of 32 selects instead of five
//   stage 'objects' (forward, one position per object): sees = inherited & groups != 0, or the object lies in a
//                            granted folder's interval; count += sees, bad += sees && under /finance && !member
// The outputs, viewable and violations, are a u32 output group.
import {type AnyStage, type LoopProgram, type WordBinding, createWordStage} from '../../vendor/handwired/src/json-search/loop-program.ts'
import {type Word, WordCircuit} from '../../vendor/handwired/src/runtime/words.ts'
import {GROUPS, type Org, closure as close, derive} from '../next/rebac/model.ts'
import {packStage} from './enum.ts'

export const CELLS = 4 // groups (low 16 bits), groups (high 16 bits), grant 0 + 1, grant 1 + 1

// pack: one output word per user, violations << 12 | viewable (both at most 2,048 objects), instead of two.
export function buildRebac(org: Org, derived = derive(org), pack = false): LoopProgram<AnyStage> {
  const O = org.objects
  const regs = ['groups', 'lo0', 'hi0', 'lo1', 'hi1', 'member', 'count', 'bad']
  const reg = (name: string) => regs.indexOf(name)

  // The closure stage. Sources: 4 cells, then tin (O), tout (O), star (GROUPS: R^5 of each group) and the Finance
  // mask, shared.
  const TIN = CELLS, TOUT = TIN + O, SUB = TOUT + O, FIN = SUB + GROUPS
  const c = new WordCircuit(FIN + 1)
  const k = (n: number) => c.constant(n >>> 0)
  const direct = c.or(c.shl(c.source(1), k(16)), c.source(0))
  let groups = direct
  for (let g = 0; g < GROUPS; g++) groups = c.or(groups, c.select(c.and(c.shr(direct, k(g)), k(1)), c.source(SUB + g), k(0)))
  // A grant's interval, or the empty one (lo = 1, hi = 0) for none.
  // Grants are object + 1 (at most O), so object = plus ∸ 1 is a proven index into the interval tables.
  c.assumeAtMost(c.source(2), O)
  c.assumeAtMost(c.source(3), O)
  const interval = (cell: number) => {
    const plus = c.source(cell), none = c.eq(plus, k(0)), object = c.monus(plus, k(1))
    return [c.select(none, k(1), c.load(TIN, O, object)), c.select(none, k(0), c.load(TOUT, O, object))] as const
  }
  const [lo0, hi0] = interval(2), [lo1, hi1] = interval(3)
  const member = c.ne(c.and(groups, c.source(FIN)), k(0))
  const closure = createWordStage({
    name: 'closure', repeat: 'once', circuit: c, sharedOffset: 0,
    bindings: new Map(Array.from({length: CELLS}, (_, column) => [c.source(column), {kind: 'cell' as const, buffer: 0, column}])),
    outputs: [
      ...([['groups', groups], ['lo0', lo0], ['hi0', hi0], ['lo1', lo1], ['hi1', hi1], ['member', member]] as const).map(([name, wire]) => ({wire, write: {kind: 'register' as const, register: reg(name)}})),
      {wire: k(0), write: {kind: 'register', register: reg('count')}},
      {wire: k(0), write: {kind: 'register', register: reg('bad')}},
    ],
  })

  // The objects stage. Sources: the registers, the position, then inherited (O) and tin with the under-/finance bit on
  // top (O: tin | uf << 31; an Euler time is below 2 × O), shared. One read gives both: a third table read per object
  // was the whole gap to the hand-written shader, which reads under /finance only for an object the user sees.
  const R = regs.length, POS = R, INH = R + 1, TIN2 = INH + O
  const w = new WordCircuit(TIN2 + O)
  const r = (name: string) => w.source(reg(name)) as Word
  const o = w.source(POS), one = w.constant(1), zero = w.constant(0)
  w.assumeAtMost(o, O - 1) // the position: every table read below is in range, so none needs a bounds check
  const tinUf = w.load(TIN2, O, o), t = w.and(tinUf, w.constant(0x7fffffff)), underFinance = w.shr(tinUf, w.constant(31))
  const within = (lo: Word, hi: Word) => w.and(w.le(lo, t), w.le(t, hi))
  const sees = w.or(w.ne(w.and(w.load(INH, O, o), r('groups')), zero), w.or(within(r('lo0'), r('hi0')), within(r('lo1'), r('hi1'))))
  const bad = w.and(sees, w.and(underFinance, w.xor(r('member'), one)))
  const objects = createWordStage({
    name: 'objects', repeat: 'forward', circuit: w, sharedOffset: FIN + 1,
    bindings: new Map<Word, WordBinding>([...regs.map((_, register) => [w.source(register), {kind: 'register' as const, register}] as const), [o, {kind: 'position' as const}]]),
    outputs: [
      {wire: w.add(r('count'), sees), write: {kind: 'register', register: reg('count')}},
      {wire: w.add(r('bad'), bad), write: {kind: 'register', register: reg('bad')}},
    ],
  })

  // Shared words: the closure stage's table, then the objects stage's.
  const shared = new Float32Array(FIN + 1 + TIN2 + O + (pack ? 2 : 0))
  const words = new Uint32Array(shared.buffer)
  words.set(Uint32Array.from(derived.tin), TIN)
  words.set(Uint32Array.from(derived.tout), TOUT)
  words.set(Uint32Array.from({length: GROUPS}, (_, g) => close((1 << g) >>> 0, org.sub)), SUB)
  words[FIN] = (1 << org.financeGroup) >>> 0
  const base = FIN + 1
  words.set(derived.inherited, base + INH)
  for (let object = 0; object < O; object++) {
    if (derived.tin[object]! >= 2 ** 31) throw new Error('an Euler time needs the top bit')
    words[base + TIN2 + object] = (derived.tin[object]! | (derived.underFinance[object]! << 31)) >>> 0
  }
  return {
    positions: O, buffers: [{name: 'users', cellsPerDocument: CELLS}],
    registers: regs.map(name => ({name, initial: 0, type: 'u32' as const})), fields: [],
    outputGroups: [{name: 'audit', kind: 'document', valuesPerDocument: pack ? 1 : 2, fill: 0, type: 'u32'}],
    stages: pack ? [closure, objects, packStage(reg('bad'), reg('count'), FIN + 1 + TIN2 + O)] : [closure, objects],
    results: pack ? [] : [{group: 0, column: 0, register: reg('count')}, {group: 0, column: 1, register: reg('bad')}],
    sharedValues: shared, lengthCell: undefined,
  }
}

// The users' cells for the document store.
export function userCells(org: Org, users = org.users): Float32Array {
  const cells = new Float32Array(users * CELLS)
  for (let u = 0; u < users; u++) {
    const g = org.userGroups[u]!
    cells.set([g & 0xffff, g >>> 16, org.userGrant[2 * u]! + 1, org.userGrant[2 * u + 1]! + 1], u * CELLS)
  }
  return cells
}
