import {Kind, Term, Cond, lit, when, all, any, type Raw} from './dsl.ts'
import {divideFixed} from './fixed-division.ts'

export type FixedWidth = 8 | 16 | 32 | 64
export type Overflow = 'WRAP' | 'SATURATE' | 'TRAP'
export type DivisionRounding = 'FLOOR' | 'TRUNCATING' | 'EUCLIDEAN'
const validKind = (width: FixedWidth, signed: boolean): void => {
  if (![8, 16, 32, 64].includes(width)) throw new RangeError('fixed width must be 8, 16, 32, or 64')
  if (typeof signed !== 'boolean') throw new TypeError('fixed signedness must be boolean')
}
const base = (w: FixedWidth) => w === 8 ? 256 : 65536
const digits = (w: FixedWidth) => w === 8 ? 1 : w / 16
const falseCond = () => lit(0).eq(1)
// Store lowers a word to plain Terms. Keep its failure on fresh wrappers rather
// than mutating the shared limbs, which may also belong to an untrapped word.
const storedTermFailures = new WeakMap<Term, Cond>()
const validMode = (mode: Overflow): void => {
  if (mode !== 'WRAP' && mode !== 'SATURATE' && mode !== 'TRAP') throw new RangeError('an explicit overflow mode is required')
}
const failures = (...cs: (Cond | undefined)[]): Cond | undefined => {
  const present = cs.filter((c): c is Cond => c !== undefined)
  return present.length ? any(...present) : undefined
}
const select = (c: Cond, a: readonly Term[], b: readonly Term[]) => a.map((x, i) => when(c, x, b[i]!))
const constant = (w: FixedWidth, signed: boolean, value: bigint): readonly Term[] => {
  const mod = 1n << BigInt(w)
  let x = ((value % mod) + mod) % mod
  const radix = BigInt(base(w))
  return Array.from({length: digits(w)}, () => { const d = Number(x % radix); x /= radix; return lit(d) })
}
const equal = (a: readonly Term[], b: readonly Term[]) => all(...a.map((x, i) => x.eq(b[i]!)))
const less = (a: readonly Term[], b: readonly Term[]) => {
  let result = falseCond()
  for (let i = 0; i < a.length; i++) result = any(a[i]!.lt(b[i]!), all(a[i]!.eq(b[i]!), result))
  return result
}
const addRaw = (a: readonly Term[], b: readonly Term[], radix: number): {low: Term[], carry: Term} => {
  let carry = lit(0)
  const low: Term[] = []
  for (let i = 0; i < a.length; i++) {
    const sum = a[i]!.plus(b[i]!).plus(carry) // at most 2*65535+1
    low.push(sum.modBy(radix))
    carry = sum.divBy(radix)
  }
  return {low, carry}
}
const invert = (xs: readonly Term[], radix: number) => xs.map(x => lit(radix - 1).minus(x))
const negateRaw = (xs: readonly Term[], radix: number) => addRaw(invert(xs, radix), [lit(1), ...Array.from({length: xs.length - 1}, () => lit(0))], radix).low
const signOf = (xs: readonly Term[], radix: number) => xs[xs.length - 1]!.atLeast(radix / 2)
const magnitude = (xs: readonly Term[], radix: number, negative: Cond) => select(negative, negateRaw(xs, radix), xs)
const maxWord = (w: FixedWidth, signed: boolean) => constant(w, signed, (1n << BigInt(w - (signed ? 1 : 0))) - 1n)
const minWord = (w: FixedWidth, signed: boolean) => constant(w, signed, signed ? -(1n << BigInt(w - 1)) : 0n)
const rawBigInt = (w: FixedWidth, signed: boolean, xs: readonly Term[]): bigint | undefined => {
  if (xs.some(x => x.val === undefined)) return undefined
  let n = 0n
  for (let i = xs.length - 1; i >= 0; i--) n = n * BigInt(base(w)) + BigInt(xs[i]!.val!)
  return signed && n >= (1n << BigInt(w - 1)) ? n - (1n << BigInt(w)) : n
}
const parse = (w: FixedWidth, signed: boolean, raw: Raw | bigint): bigint => {
  if (typeof raw === 'number') {
    if (w === 64 || !Number.isSafeInteger(raw)) throw new RangeError('unsafe or 64-bit number: use a decimal string or bigint')
  } else if (typeof raw !== 'string' && typeof raw !== 'bigint') throw new TypeError('fixed integer requires an integer or decimal string')
  if (typeof raw === 'string' && !/^-?(0|[1-9][0-9]*)$/.test(raw)) throw new RangeError('fixed integer requires a decimal integer string')
  const n = BigInt(raw)
  const lo = signed ? -(1n << BigInt(w - 1)) : 0n
  const hi = (1n << BigInt(w - (signed ? 1 : 0))) - 1n
  if (n < lo || n > hi) throw new RangeError(`${n} outside ${signed ? 'signed' : 'unsigned'} ${w}-bit range`)
  return n
}

export class FixedWord {
  constructor(readonly width: FixedWidth, readonly signed: boolean, readonly limbs: readonly Term[], readonly failure?: Cond) {
    validKind(width, signed)
    if (limbs.length !== digits(width)) throw new RangeError('incorrect fixed integer limb count')
  }
  private check(other: FixedWord) {
    if (!(other instanceof FixedWord)) throw new TypeError('fixed integer operand required')
    if (this.width !== other.width || this.signed !== other.signed) throw new TypeError('fixed integers must have identical width and signedness; cast explicitly')
  }
  private finish(low: readonly Term[], overflow: Cond, mode: Overflow, negative: Cond, inherited?: Cond): FixedWord {
    validMode(mode)
    const result = mode === 'SATURATE' ? select(overflow, select(negative, minWord(this.width, this.signed), maxWord(this.width, this.signed)), low) : low
    return new FixedWord(this.width, this.signed, result, failures(inherited, mode === 'TRAP' ? overflow : undefined))
  }
  private checkComparison(b: FixedWord): void {
    this.check(b)
    // A Cond has no failure channel. A comparison of a possibly trapped result
    // must not erase its failure and accidentally establish a law about that result.
    if ((this.failure && this.failure.ok !== false) || (b.failure && b.failure.ok !== false))
      throw new Error('fixed integer comparison may discard a failure; handle the failure first')
  }
  eq(b: FixedWord): Cond { this.checkComparison(b); return equal(this.limbs, b.limbs) }
  ne(b: FixedWord): Cond { return this.eq(b).not() }
  lt(b: FixedWord): Cond {
    this.checkComparison(b)
    const aNeg = this.signed ? signOf(this.limbs, base(this.width)) : falseCond()
    const bNeg = this.signed ? signOf(b.limbs, base(this.width)) : falseCond()
    return this.signed ? any(all(aNeg, bNeg.not()), all(aNeg.iff(bNeg), less(this.limbs, b.limbs))) : less(this.limbs, b.limbs)
  }
  atMost(b: FixedWord): Cond { return any(this.lt(b), this.eq(b)) }
  gt(b: FixedWord): Cond { return b.lt(this) }
  atLeast(b: FixedWord): Cond { return b.atMost(this) }
  plus(b: FixedWord, mode: Overflow): FixedWord {
    validMode(mode)
    this.check(b)
    const {low, carry} = addRaw(this.limbs, b.limbs, base(this.width))
    const na = signOf(this.limbs, base(this.width)), nb = signOf(b.limbs, base(this.width)), nr = signOf(low, base(this.width))
    const over = this.signed ? all(na.iff(nb), na.iff(nr).not()) : carry.eq(1)
    return this.finish(low, over, mode, this.signed ? na : falseCond(), failures(this.failure, b.failure))
  }
  minus(b: FixedWord, mode: Overflow): FixedWord {
    validMode(mode)
    this.check(b)
    // Add the complement and one; carry=0 iff unsigned subtraction borrowed.
    const radix = base(this.width)
    const complement = invert(b.limbs, radix)
    const {low, carry} = addRaw(this.limbs, complement, radix)
    const incremented = addRaw(low, [lit(1), ...Array.from({length: low.length - 1}, () => lit(0))], radix)
    const noBorrow = any(carry.eq(1), incremented.carry.eq(1))
    const na = signOf(this.limbs, radix), nb = signOf(b.limbs, radix), nr = signOf(incremented.low, radix)
    const over = this.signed ? all(na.iff(nb).not(), nr.iff(na).not()) : noBorrow.not()
    return this.finish(incremented.low, over, mode, this.signed ? na : lit(0).eq(0), failures(this.failure, b.failure))
  }
  negate(mode: Overflow): FixedWord { return new FixedWord(this.width, this.signed, constant(this.width, this.signed, 0n)).minus(this, mode) }
  mul(b: FixedWord, mode: Overflow): FixedWord {
    validMode(mode)
    this.check(b)
    const radix = base(this.width), n = this.limbs.length
    const an = this.signed ? signOf(this.limbs, radix) : falseCond()
    const bn = this.signed ? signOf(b.limbs, radix) : falseCond()
    const a = this.signed ? magnitude(this.limbs, radix, an) : this.limbs
    const bb = this.signed ? magnitude(b.limbs, radix, bn) : b.limbs
    const out: Term[] = []
    let carry = lit(0)
    for (let k = 0; k < 2 * n; k++) {
      let col = carry
      for (let i = Math.max(0, k - n + 1); i <= Math.min(k, n - 1); i++) col = col.plus(a[i]!.mul(bb[k - i]!))
      // At most 4*65535²+4*65535 < 2^35; no intermediate exceeds 2^53.
      out.push(col.modBy(radix))
      carry = col.divBy(radix)
    }
    const productNegative = an.iff(bn).not()
    const upper = out.slice(n)
    const limit = constant(this.width, this.signed, 1n << BigInt(this.width - 1))
    const positiveLimit = maxWord(this.width, this.signed)
    const magnitudeLow = out.slice(0, n)
    const high = any(...upper.map(x => x.ne(0)))
    const overflow = this.signed
      ? any(high, all(productNegative, less(limit, magnitudeLow)), all(productNegative.not(), less(positiveLimit, magnitudeLow)))
      : high
    const low = this.signed ? select(productNegative, negateRaw(magnitudeLow, radix), magnitudeLow) : magnitudeLow
    return this.finish(low, overflow, mode, productNegative, failures(this.failure, b.failure))
  }
  cast(width: FixedWidth, signed: boolean, mode: Overflow): FixedWord {
    validMode(mode)
    validKind(width, signed)
    const radix = base(this.width), negative = this.signed ? signOf(this.limbs, radix) : falseCond()
    const mag = this.signed ? magnitude(this.limbs, radix, negative) : this.limbs
    // Conversion of limbs uses only <=65535*256 and division by the constant radix.
    let source = mag
    if (radix !== base(width)) source = width === 8 ? [mag[0]!.modBy(256)] : [mag[0]!]
    const low = Array.from({length: digits(width)}, (_, i) => source[i] ?? lit(0))
    const sourceHigh = mag.slice(digits(width))
    const high = any(...sourceHigh.map(x => x.ne(0)), ...(radix !== base(width) && width === 8 ? [mag[0]!.divBy(256).ne(0)] : []))
    const limit = signed ? constant(width, true, 1n << BigInt(width - 1)) : maxWord(width, false)
    const overflow = any(high, all(negative, signed ? less(limit, low) : lit(0).eq(0)), all(negative.not(), less(signed ? maxWord(width, true) : maxWord(width, false), low)))
    const twos = negative.ok === false ? low : select(negative, negateRaw(low, base(width)), low)
    const result = mode === 'SATURATE' ? select(overflow, select(negative, minWord(width, signed), maxWord(width, signed)), twos) : twos
    return new FixedWord(width, signed, result, failures(this.failure, mode === 'TRAP' ? overflow : undefined))
  }
  div(b: FixedWord, rounding: DivisionRounding, mode: Overflow): FixedWord { return this.divide(b, rounding, mode, false) }
  rem(b: FixedWord, rounding: DivisionRounding, mode: Overflow): FixedWord { return this.divide(b, rounding, mode, true) }
  private divide(b: FixedWord, rounding: DivisionRounding, mode: Overflow, remainder: boolean): FixedWord {
    this.check(b)
    validMode(mode)
    if (!['FLOOR', 'TRUNCATING', 'EUCLIDEAN'].includes(rounding)) throw new RangeError('unknown division rounding')
    const aVal = rawBigInt(this.width, this.signed, this.limbs)
    const bVal = rawBigInt(b.width, b.signed, b.limbs)
    if (aVal === undefined || bVal === undefined) return divideFixed(this, b, rounding, mode, remainder)
    const min = this.signed ? -(1n << BigInt(this.width - 1)) : 0n
    const zero = bVal === 0n
    const overflow = this.signed && aVal === min && bVal === -1n
    let q = zero ? 0n : aVal / bVal
    let r = zero ? 0n : aVal % bVal
    if (!zero && r !== 0n) {
      if (rounding === 'FLOOR' && ((r < 0n) !== (bVal < 0n))) { q--; r += bVal }
      if (rounding === 'EUCLIDEAN' && r < 0n) { q -= bVal < 0n ? -1n : 1n; r += bVal < 0n ? -bVal : bVal }
    }
    if (overflow) { q = mode === 'SATURATE' ? -min - 1n : min; r = 0n }
    const divZero = zero ? lit(0).eq(0) : falseCond()
    const trapOverflow = overflow && mode === 'TRAP' ? lit(0).eq(0) : undefined
    return new FixedWord(this.width, this.signed, constant(this.width, this.signed, remainder ? r : q), failures(this.failure, b.failure, divZero, trapOverflow))
  }
}

export const fixedFailure = (value: unknown): Cond | undefined =>
  value instanceof FixedWord ? value.failure : value instanceof Term ? storedTermFailures.get(value) : undefined
export const fixedSelect = (condition: Cond, a: FixedWord, b: FixedWord): FixedWord => {
  if (a.width !== b.width || a.signed !== b.signed) throw new TypeError('selected fixed integers need identical kinds')
  const failure = a.failure || b.failure ? any(all(condition, a.failure ?? falseCond()), all(condition.not(), b.failure ?? falseCond())) : undefined
  return new FixedWord(a.width, a.signed, select(condition, a.limbs, b.limbs), failure)
}

export const fixedInt = (width: FixedWidth, signed: boolean): Kind<FixedWord> & {lift(value: Raw | bigint): FixedWord} => {
  validKind(width, signed)
  class FixedKind extends Kind<FixedWord> {
    vars(name: string): string[] { return Array.from({length: digits(width)}, (_, i) => `${name}$${i}`) }
    assume(name: string): Cond[] { return this.value(name).limbs.map(x => x.lt(base(width))) }
    build(name: string, get: (part: string) => Term): FixedWord { return new FixedWord(width, signed, this.vars(name).map(get)) }
    invariant(v: FixedWord): Cond[] { return v.limbs.map(x => x.lt(base(width))) }
    lift(value: Raw | bigint): FixedWord { return new FixedWord(width, signed, constant(width, signed, parse(width, signed, value))) }
    encode(name: string, raw: Raw): Record<string, number> {
      const limbs = constant(width, signed, parse(width, signed, raw))
      return Object.fromEntries(this.vars(name).map((v, i) => [v, limbs[i]!.val!]))
    }
    random(name: string, rand: (n: number) => number, _bound: number): Record<string, number> {
      return Object.fromEntries(this.vars(name).map(v => [v, rand(base(width))]))
    }
    sample(rand: (n: number) => number, bound: number): Raw {
      const n = BigInt(rand(Math.min(1 + Math.max(0, bound), signed ? base(width) / 2 : base(width))))
      return width === 64 ? n.toString() : Number(n)
    }
    store(name: string, value: unknown): Record<string, Term> {
      const word = value instanceof FixedWord ? value : this.lift(value as Raw)
      if (word.width !== width || word.signed !== signed) throw new TypeError('stored fixed integer has wrong kind')
      return Object.fromEntries(this.vars(name).map((v, i) => {
        const limb = word.limbs[i]!
        if (!word.failure) return [v, limb]
        const stored = new Term(limb.e, limb.val)
        storedTermFailures.set(stored, word.failure)
        return [v, stored]
      }))
    }
    decode(name: string, vars: Record<string, number>): Raw {
      let n = 0n
      for (const v of this.vars(name).reverse()) {
        const limb = vars[v]
        if (limb === undefined || !Number.isInteger(limb) || limb < 0 || limb >= base(width)) throw new RangeError(`invalid fixed limb ${v}`)
        n = n * BigInt(base(width)) + BigInt(limb)
      }
      if (signed && n >= 1n << BigInt(width - 1)) n -= 1n << BigInt(width)
      return width === 64 ? n.toString() : Number(n)
    }
    empty(): Raw { return width === 64 ? '0' : 0 }
  }
  return new FixedKind()
}
