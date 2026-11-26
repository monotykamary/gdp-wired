// Exact half-even decimal scaling from IEEE-754 shortest round-trip string (`String(x)`), with zero float
// multiplication. Shared by `decimal(places, {round: 'half-even'})` in `core/dsl.ts` (`encodeInput`) and emitted
// standalone TypeScript files in `core/emit.ts`.

export function scaleDecimalHalfEven(x: number | string, places: number, name: string): number {
  if (typeof x === 'number' && !Number.isFinite(x)) throw new RangeError(`${name}: expected finite decimal`)
  const raw = typeof x === 'number' ? String(x) : x.trim()
  const m = /^([+-]?)(?:(\d+)(?:\.(\d*))?|\.(\d+))(?:[eE]([+-]?\d+))?$/.exec(raw)
  if (!m) throw new RangeError(`${name}: invalid decimal ${String(x)}`)
  const neg = m[1] === '-'
  const intPart = m[2] ?? ''
  const fracPart = m[3] ?? m[4] ?? ''
  const exp = m[5] ? Number(m[5]) : 0
  if (!Number.isSafeInteger(exp)) throw new RangeError(`${name}: decimal exponent out of range`)
  const digits = (intPart + fracPart).replace(/^0+/, '')
  if (digits.length === 0) return 0
  const shift = exp - fracPart.length + places
  if (shift >= 0) {
    if (digits.length + shift > 16) throw new RangeError(`${name}: decimal out of safe integer range`)
    const n = Number(digits + '0'.repeat(shift))
    if (!Number.isSafeInteger(n)) throw new RangeError(`${name}: decimal out of safe integer range`)
    return neg && n !== 0 ? -n : n
  }
  const cut = digits.length + shift
  if (cut < 0) return 0
  if (cut > 16) throw new RangeError(`${name}: decimal out of safe integer range`)
  const wholeStr = cut === 0 ? '0' : digits.slice(0, cut)
  const firstDrop = digits[cut]!
  const rest = digits.slice(cut + 1)
  const whole = Number(wholeStr)
  if (!Number.isSafeInteger(whole)) throw new RangeError(`${name}: decimal out of safe integer range`)
  const odd = '13579'.includes(wholeStr[wholeStr.length - 1]!)
  const hasMore = /[1-9]/.test(rest)
  const up = firstDrop > '5' || (firstDrop === '5' && (hasMore || odd))
  const n = up ? whole + 1 : whole
  if (!Number.isSafeInteger(n)) throw new RangeError(`${name}: decimal out of safe integer range`)
  return neg && n !== 0 ? -n : n
}

// Emitted standalone helper, matching `scaleDecimalHalfEven` statement-for-statement (enforced by core/emit.test.ts).
export const DEC_ROUND_HELPER_LINES: readonly string[] = [
  'function $decRound(x: number, places: number, name: string): number {',
  '  if (!Number.isFinite(x)) throw new RangeError(`${name}: expected finite decimal`)',
  '  const raw = String(x)',
  '  const m = /^([+-]?)(?:(\\d+)(?:\\.(\\d*))?|\\.(\\d+))(?:[eE]([+-]?\\d+))?$/.exec(raw)',
  '  if (!m) throw new RangeError(`${name}: invalid decimal ${String(x)}`)',
  "  const neg = m[1] === '-'",
  "  const intPart = m[2] ?? ''",
  "  const fracPart = m[3] ?? m[4] ?? ''",
  '  const exp = m[5] ? Number(m[5]) : 0',
  '  if (!Number.isSafeInteger(exp)) throw new RangeError(`${name}: decimal exponent out of range`)',
  "  const digits = (intPart + fracPart).replace(/^0+/, '')",
  '  if (digits.length === 0) return 0',
  '  const shift = exp - fracPart.length + places',
  '  if (shift >= 0) {',
  '    if (digits.length + shift > 16) throw new RangeError(`${name}: decimal out of safe integer range`)',
  "    const n = Number(digits + '0'.repeat(shift))",
  '    if (!Number.isSafeInteger(n)) throw new RangeError(`${name}: decimal out of safe integer range`)',
  '    return neg && n !== 0 ? -n : n',
  '  }',
  '  const cut = digits.length + shift',
  '  if (cut < 0) return 0',
  '  if (cut > 16) throw new RangeError(`${name}: decimal out of safe integer range`)',
  "  const wholeStr = cut === 0 ? '0' : digits.slice(0, cut)",
  '  const firstDrop = digits[cut]!',
  '  const rest = digits.slice(cut + 1)',
  '  const whole = Number(wholeStr)',
  '  if (!Number.isSafeInteger(whole)) throw new RangeError(`${name}: decimal out of safe integer range`)',
  "  const odd = '13579'.includes(wholeStr[wholeStr.length - 1]!)",
  '  const hasMore = /[1-9]/.test(rest)',
  "  const up = firstDrop > '5' || (firstDrop === '5' && (hasMore || odd))",
  '  const n = up ? whole + 1 : whole',
  '  if (!Number.isSafeInteger(n)) throw new RangeError(`${name}: decimal out of safe integer range`)',
  '  return neg && n !== 0 ? -n : n',
  '}',
]
