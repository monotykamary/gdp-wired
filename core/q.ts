// Exact rationals (bigint fractions), untrusted: what the rational solver's witnesses, the rational rules' runtimes
// and builder compute with. The kernel normalizes its constants on its own (kernel.ts's ratNorm). Every value here is
// reduced, with a positive denominator, so equal rationals are equal pairs.
import type {Rat} from '../kernel/kernel.ts'

export type {Rat}
export const bgcd = (a: bigint, b: bigint): bigint => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a }
export const q = (num: bigint | number, den: bigint | number = 1n): Rat => {
  let n = BigInt(num), d = BigInt(den)
  if (d === 0n) throw new RangeError('a rational with denominator 0')
  if (d < 0n) { n = -n; d = -d }
  const g = bgcd(n, d) || 1n
  return {num: n / g, den: d / g}
}
export const Q0 = q(0), Q1 = q(1)
export const qadd = (a: Rat, b: Rat): Rat => q(a.num * b.den + b.num * a.den, a.den * b.den)
export const qsub = (a: Rat, b: Rat): Rat => q(a.num * b.den - b.num * a.den, a.den * b.den)
export const qmul = (a: Rat, b: Rat): Rat => q(a.num * b.num, a.den * b.den)
export const qdiv = (a: Rat, b: Rat): Rat => q(a.num * b.den, a.den * b.num)
export const qneg = (a: Rat): Rat => ({num: -a.num, den: a.den})
export const qcmp = (a: Rat, b: Rat): number => { const d = a.num * b.den - b.num * a.den; return d < 0n ? -1 : d > 0n ? 1 : 0 }
export const qeq = (a: Rat, b: Rat): boolean => a.num === b.num && a.den === b.den
export const qmin = (a: Rat, b: Rat): Rat => (qcmp(a, b) <= 0 ? a : b)
export const qmax = (a: Rat, b: Rat): Rat => (qcmp(a, b) <= 0 ? b : a)
export const qnum = (a: Rat): number => Number(a.num) / Number(a.den)
export const qshow = (a: Rat): string => (a.den === 1n ? String(a.num) : `${a.num}/${a.den}`)
// A decimal as written ("12.50", "-0.1", "1e-3"), a fraction ("1/3"), an integer, or a number read as its shortest
// decimal text (0.1 is 1/10, not the double nearest it).
export function qparse(x: number | string | bigint | Rat): Rat {
  if (typeof x === 'object') return q(x.num, x.den)
  if (typeof x === 'bigint') return q(x)
  if (typeof x === 'number' && !Number.isFinite(x)) throw new RangeError(`${x} is not a rational`)
  const text = String(x).trim()
  const frac = /^(-?\d+)\s*\/\s*(\d+)$/.exec(text)
  if (frac) return q(BigInt(frac[1]!), BigInt(frac[2]!))
  const m = /^(-?)(\d*)(?:\.(\d*))?(?:e([+-]?\d+))?$/i.exec(text)
  if (!m || (!m[2] && !m[3])) throw new RangeError(`${text} is not a rational (a decimal like 12.5, or a fraction like 1/3)`)
  const digits = BigInt(`${m[2] || '0'}${m[3] ?? ''}`), exp = Number(m[4] ?? 0) - (m[3]?.length ?? 0)
  const v = exp >= 0 ? q(digits * 10n ** BigInt(exp)) : q(digits, 10n ** BigInt(-exp))
  return m[1] ? qneg(v) : v
}
// The value of a sum Σ c·x + c₀ with integer coefficients (a solver's row) at a rational point.
export const qrow = (lin: Record<string, number>, at: Record<string, Rat>): Rat => {
  let out = Q0
  for (const [key, c] of Object.entries(lin)) out = qadd(out, qmul(q(c), key === '1' ? Q1 : (at[key] ?? Q0)))
  return out
}
