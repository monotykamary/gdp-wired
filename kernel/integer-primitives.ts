// Exact, bounded machine-integer semantics. No Number is accepted as an operand.
export type Width = 8 | 16 | 32 | 64
export type OverflowMode = 'WRAP' | 'SATURATE' | 'TRAP'
export type DivisionMode = 'FLOOR' | 'TRUNCATING' | 'EUCLIDEAN'
export type PrimitiveOperation = 'add' | 'sub' | 'mul' | 'neg' | 'cast' | 'div' | 'rem'
export type PrimitiveSpec = {
  width: Width
  signed: boolean
  operation: PrimitiveOperation
  overflow: OverflowMode
  division?: DivisionMode
}
export type PrimitiveResult = {ok: true, value: bigint} | {ok: false, reason: string}
export type PrimitiveReceipt = {
  spec: PrimitiveSpec | null // null if the input spec failed validation
  a: string
  b?: string
  result: {ok: true, value: string} | {ok: false, reason: string}
}

const fail = (reason: string): PrimitiveResult => ({ok: false, reason})
const own = (o: object, k: string): boolean => Object.prototype.hasOwnProperty.call(o, k)
const binary = (op: PrimitiveOperation): boolean => op === 'add' || op === 'sub' || op === 'mul' || op === 'div' || op === 'rem'
const dividing = (op: PrimitiveOperation): boolean => op === 'div' || op === 'rem'

type Snapshot = {ok: true, spec: PrimitiveSpec} | {ok: false, reason: string}
function snapshot(spec: unknown): Snapshot {
  if (spec === null || typeof spec !== 'object') return {ok: false, reason: 'invalid spec'}
  let s: Record<string, unknown>
  try {
    const proto = Object.getPrototypeOf(spec)
    if (proto !== Object.prototype && proto !== null) return {ok: false, reason: 'invalid spec'}
    const ds = Object.getOwnPropertyDescriptors(spec)
    const keys = Reflect.ownKeys(ds)
    if (keys.some(k => typeof k !== 'string')) return {ok: false, reason: 'invalid spec'}
    s = Object.create(null) as Record<string, unknown>
    for (const k of keys as string[]) {
      if (!['width', 'signed', 'operation', 'overflow', 'division'].includes(k)) return {ok: false, reason: 'unknown spec field'}
      const d = ds[k]!
      if (!own(d, 'value')) return {ok: false, reason: 'invalid spec'}
      s[k] = d.value
    }
  } catch { return {ok: false, reason: 'invalid spec'} }
  if (!own(s, 'width') || ![8, 16, 32, 64].includes(s.width as number)) return {ok: false, reason: 'invalid width'}
  if (!own(s, 'signed') || typeof s.signed !== 'boolean') return {ok: false, reason: 'invalid signed flag'}
  if (!own(s, 'operation') || !['add', 'sub', 'mul', 'neg', 'cast', 'div', 'rem'].includes(s.operation as string)) return {ok: false, reason: 'invalid operation'}
  if (!own(s, 'overflow') || !['WRAP', 'SATURATE', 'TRAP'].includes(s.overflow as string)) return {ok: false, reason: 'invalid overflow mode'}
  const hasDivision = own(s, 'division')
  if (hasDivision !== dividing(s.operation as PrimitiveOperation) ||
      (hasDivision && !['FLOOR', 'TRUNCATING', 'EUCLIDEAN'].includes(s.division as string))) return {ok: false, reason: 'invalid division mode'}
  const clean: PrimitiveSpec = {width: s.width as Width, signed: s.signed as boolean, operation: s.operation as PrimitiveOperation, overflow: s.overflow as OverflowMode}
  if (hasDivision) clean.division = s.division as DivisionMode
  return {ok: true, spec: clean}
}

export function evaluatePrimitive(spec: PrimitiveSpec, a: bigint, b?: bigint): PrimitiveResult {
  const parsed = snapshot(spec)
  return parsed.ok ? evaluateSnapshot(parsed.spec, a, b) : fail(parsed.reason)
}

function evaluateSnapshot(spec: PrimitiveSpec, a: bigint, b?: bigint): PrimitiveResult {
  if (typeof a !== 'bigint') return fail('a must be bigint')
  const needsB = binary(spec.operation)
  if (needsB ? typeof b !== 'bigint' : b !== undefined) return fail(needsB ? 'b must be bigint' : 'unexpected b')
  const bits = BigInt(spec.width)
  const modulus = 1n << bits
  const min = spec.signed ? -(modulus >> 1n) : 0n
  const max = spec.signed ? (modulus >> 1n) - 1n : modulus - 1n
  // Cast is conversion from an unbounded exact integer; other operands are values of this type.
  if (spec.operation !== 'cast' && (a < min || a > max)) return fail('a out of bounds')
  if (needsB && (b! < min || b! > max)) return fail('b out of bounds')
  let raw: bigint
  switch (spec.operation) {
    case 'add': raw = a + b!; break
    case 'sub': raw = a - b!; break
    case 'mul': raw = a * b!; break
    case 'neg': raw = -a; break
    case 'cast': raw = a; break
    case 'div':
    case 'rem': {
      if (b === 0n) return fail('division by zero')
      let q = a / b! // BigInt division truncates towards zero.
      let r = a % b!
      if (spec.division === 'FLOOR' && r !== 0n && ((r < 0n) !== (b! < 0n))) {
        q -= 1n; r += b!
      } else if (spec.division === 'EUCLIDEAN' && r < 0n) {
        const sign = b! < 0n ? -1n : 1n
        q -= sign; r += b! * sign
      }
      // Division-pair trap: even rem(MIN, -1) fails when its quotient overflows.
      // WRAP/SATURATE still return the exact remainder (zero in that case).
      if (spec.operation === 'rem' && spec.overflow === 'TRAP' && (q < min || q > max)) return fail('overflow')
      raw = spec.operation === 'div' ? q : r
      break
    }
  }
  if (raw >= min && raw <= max) return {ok: true, value: raw}
  if (spec.overflow === 'TRAP') return fail('overflow')
  if (spec.overflow === 'SATURATE') return {ok: true, value: raw < min ? min : max}
  const unsigned = ((raw % modulus) + modulus) % modulus
  return {ok: true, value: spec.signed && unsigned >= (modulus >> 1n) ? unsigned - modulus : unsigned}
}

// Bounded wrap case certificate: an independently checked exact identity, not a proof
// of a universal law or a coupling to core E. All certificate integers are exact.
export type WrapCaseCertificate = {quotient: bigint, residue: bigint, value: bigint}
export function checkWrapCase(spec: PrimitiveSpec, a: bigint, b: bigint | undefined, c: WrapCaseCertificate): boolean {
  const parsed = snapshot(spec)
  if (!parsed.ok) return false
  const s = parsed.spec
  if (s.overflow !== 'WRAP' || !['add', 'sub', 'mul', 'neg', 'cast'].includes(s.operation)) return false
  if (typeof a !== 'bigint' || c === null || typeof c !== 'object') return false
  let q: bigint, u: bigint, y: bigint
  try {
    if (Object.getPrototypeOf(c) !== Object.prototype && Object.getPrototypeOf(c) !== null) return false
    const ds = Object.getOwnPropertyDescriptors(c)
    if (Reflect.ownKeys(ds).length !== 3 || !['quotient', 'residue', 'value'].every(k => own(ds, k) && own(ds[k]!, 'value') && typeof ds[k]!.value === 'bigint')) return false
    q = ds.quotient!.value as bigint
    u = ds.residue!.value as bigint
    y = ds.value!.value as bigint
  } catch { return false }
  const m = 1n << BigInt(s.width), half = m >> 1n
  const lo = s.signed ? -half : 0n, hi = s.signed ? half - 1n : m - 1n
  if (s.operation !== 'cast' && (a < lo || a > hi)) return false
  if (binary(s.operation) ? typeof b !== 'bigint' || b < lo || b > hi : b !== undefined) return false
  let raw: bigint
  switch (s.operation) {
    case 'add': raw = a + b!; break
    case 'sub': raw = a - b!; break
    case 'mul': raw = a * b!; break
    case 'neg': raw = -a; break
    case 'cast': raw = a; break
    case 'div': case 'rem': return false
  }
  return u >= 0n && u < m && raw === q * m + u &&
    y === (s.signed && u >= half ? u - m : u) && y >= lo && y <= hi &&
    raw - y === (q + (s.signed && u >= half ? 1n : 0n)) * m
}

// Valid operands/results cross JSON as exact decimal strings. An invalid supplied
// operand is explicitly marked <invalid>, never silently changed into an absent one.
// Diagnostic receipts are not proof certificates and must not be accepted as such.
export function evaluatePrimitiveReceipt(spec: PrimitiveSpec, a: bigint, b?: bigint): PrimitiveReceipt {
  const parsed = snapshot(spec)
  const result = parsed.ok ? evaluateSnapshot(parsed.spec, a, b) : fail(parsed.reason)
  return {
    spec: parsed.ok ? parsed.spec : null, a: typeof a === 'bigint' ? a.toString(10) : '<invalid>',
    ...(b === undefined ? {} : {b: typeof b === 'bigint' ? b.toString(10) : '<invalid>'}),
    result: result.ok ? {ok: true, value: result.value.toString(10)} : result,
  }
}
