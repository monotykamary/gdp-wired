import {FixedWord, fixedSelect, type DivisionRounding, type Overflow} from './fixed-integers.ts'
import {Term, Cond, all, any, lit} from './dsl.ts'
import {wordDivisionKey, wordDivisionName} from '../kernel/word-division.ts'
export {wordDivisionKey, wordDivisionName} from '../kernel/word-division.ts'
type C = Cond['c']

// Preserve the capture API for DSL assembly; intrinsic getters need no flags.
let active: Record<string, C> | undefined
export function captureFixed<T>(f: () => T): {value: T, flags: Record<string, C>} {
  const previous = active, flags: Record<string, C> = Object.create(null)
  active = flags
  try { return {value: f(), flags} }
  finally { active = previous }
}

const zero = () => lit(0)
const no = () => zero().eq(1)
const radixOf = (a: FixedWord) => a.width === 8 ? 256 : 65536
const pure = (w: FixedWord, signed = w.signed) => new FixedWord(w.width, signed, w.limbs)
const same = (a: readonly Term[], b: readonly Term[]) => all(...a.map((x, i) => x.eq(b[i]!)))
const nonzero = (a: readonly Term[]) => any(...a.map(x => x.ne(0)))
const neg = (a: FixedWord) => pure(a).negate('WRAP')
const sign = (a: FixedWord) => a.limbs[a.limbs.length - 1]!.atLeast(radixOf(a) / 2)
// Intrinsic quotients and residues are keyed by both unsigned magnitudes.
// Known inputs use BigInt for metadata; symbolic limbs leave val undefined.
const magnitude = (limbs: readonly Term[], radix: bigint): bigint | undefined => {
  let value = 0n
  for (let i = limbs.length - 1; i >= 0; i--) {
    const digit = limbs[i]!.val
    if (digit === undefined) return undefined
    value = value * radix + BigInt(digit)
  }
  return value
}
const select = (c: Cond, a: FixedWord, b: FixedWord) => fixedSelect(c, a, b)

export function divideFixed(a: FixedWord, b: FixedWord, rounding: DivisionRounding, mode: Overflow, remainder: boolean): FixedWord {
  if (!(a instanceof FixedWord) || !(b instanceof FixedWord) || a.width !== b.width || a.signed !== b.signed)
    throw new TypeError('fixed integers must have identical width and signedness')
  if (!['WRAP', 'SATURATE', 'TRAP'].includes(mode)) throw new RangeError('an explicit overflow mode is required')
  if (!['FLOOR', 'TRUNCATING', 'EUCLIDEAN'].includes(rounding)) throw new RangeError('unknown division rounding')
  if (!active) throw new Error('symbolic fixed integer division requires captureFixed')
  const radix = radixOf(a), n = a.limbs.length
  const aa = pure(a), bb = pure(b)
  const aNeg = a.signed ? sign(aa) : no(), bNeg = b.signed ? sign(bb) : no()
  const am = pure(a.signed ? select(aNeg, neg(aa), aa) : aa, false)
  const bm = pure(b.signed ? select(bNeg, neg(bb), bb) : bb, false)
  const key = wordDivisionKey([...am.limbs, ...bm.limbs].map(x => x.e))
  const av = magnitude(am.limbs, BigInt(radix)), bv = magnitude(bm.limbs, BigInt(radix))
  if (bv === 0n) return new FixedWord(a.width, a.signed, Array.from({length: n}, zero), zero().eq(0))
  const qv = av === undefined || bv === undefined ? undefined : av / bv
  const rv = av === undefined || bv === undefined ? undefined : av % bv
  const digits = (kind: 'q' | 'r', value: bigint | undefined) => Array.from({length: n}, (_, i) =>
    new Term({op: 'get', map: wordDivisionName(a.width, kind, i), key},
      value === undefined ? undefined : Number(value / (BigInt(radix) ** BigInt(i)) % BigInt(radix))))
  const uq = new FixedWord(a.width, false, digits('q', qv))
  const ur = new FixedWord(a.width, false, digits('r', rv))
  const qNegative = a.signed ? aNeg.iff(bNeg).not() : no()
  let q = a.signed ? select(qNegative, neg(pure(uq, true)), pure(uq, true)) : uq
  let r = a.signed ? select(aNeg, neg(pure(ur, true)), pure(ur, true)) : ur
  const rNotZero = nonzero(ur.limbs)
  if (a.signed && rounding === 'FLOOR') {
    const adjust = all(rNotZero, qNegative)
    q = select(adjust, q.minus(new FixedWord(a.width, true, [lit(1), ...Array.from({length: n - 1}, zero)]), 'WRAP'), q)
    r = select(adjust, r.plus(bb, 'WRAP'), r)
  } else if (a.signed && rounding === 'EUCLIDEAN') {
    const adjust = all(rNotZero, aNeg)
    const one = new FixedWord(a.width, true, [lit(1), ...Array.from({length: n - 1}, zero)])
    q = select(adjust, select(bNeg, q.plus(one, 'WRAP'), q.minus(one, 'WRAP')), q)
    r = select(adjust, r.plus(pure(bm, true), 'WRAP'), r)
  }
  const minimum = Array.from({length: n}, (_, i) => lit(i === n - 1 ? radix / 2 : 0))
  const maximum = Array.from({length: n}, (_, i) => lit(i === n - 1 ? radix / 2 - 1 : radix - 1))
  const overflow = a.signed ? all(aNeg, same(a.limbs, minimum),
    same(b.limbs, Array.from({length: n}, () => lit(radix - 1)))) : no()
  if (a.signed) {
    const min = new FixedWord(a.width, true, minimum)
    const max = new FixedWord(a.width, true, maximum)
    q = select(overflow, mode === 'SATURATE' ? max : min, q)
    r = select(overflow, new FixedWord(a.width, true, Array.from({length: n}, zero)), r)
  }
  const failure = any(...[a.failure, b.failure, nonzero(b.limbs).not(), mode === 'TRAP' ? overflow : undefined].filter((x): x is Cond => !!x))
  return new FixedWord(a.width, a.signed, (remainder ? r : q).limbs, failure)
}
