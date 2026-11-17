// Untrusted serialization only. The native Lean checker independently computes
// IntegerPrimitives.evaluate against the exact BigInt evaluator's claimed result.
import {evaluatePrimitive, evaluatePrimitiveReceipt, type PrimitiveSpec, type PrimitiveResult} from '../kernel/integer-primitives.ts'
export type {PrimitiveSpec, PrimitiveResult} from '../kernel/integer-primitives.ts'

const intLiteral = (n: bigint): string => n < 0n ? `(${n.toString(10)})` : n.toString(10)
const decimal = (n: string): bigint => {
  if (!/^-?(?:0|[1-9][0-9]*)$/.test(n)) throw new Error('expected exact decimal integer string')
  return BigInt(n)
}
const identifier = (s: string): string => {
  if (!/^[A-Za-z][A-Za-z0-9_]*$/.test(s)) throw new Error('expected Lean identifier')
  return s
}
const operation = (s: PrimitiveSpec['operation']): string => {
  if (!['add', 'sub', 'mul', 'neg', 'cast', 'div', 'rem'].includes(s)) throw new Error('invalid operation')
  return `.${s}`
}
const overflow = (s: PrimitiveSpec['overflow']): string => {
  if (!['WRAP', 'SATURATE', 'TRAP'].includes(s)) throw new Error('invalid overflow mode')
  return `.${s}`
}
const division = (s: PrimitiveSpec['division']): string => {
  if (s === undefined) return 'none'
  if (!['FLOOR', 'TRUNCATING', 'EUCLIDEAN'].includes(s)) throw new Error('invalid division mode')
  return `some .${s}`
}

/** A Lean term for the complete spec. Runtime validation remains in evaluatePrimitive. */
export function primitiveSpecLean(s: PrimitiveSpec): string {
  if (![8, 16, 32, 64].includes(s.width) || typeof s.signed !== 'boolean') throw new Error('invalid width or signed flag')
  return `{ width := ${s.width}, signed := ${s.signed}, operation := ${operation(s.operation)}, overflow := ${overflow(s.overflow)}, division := ${division(s.division)} }`
}

const errorLean = (reason: string): string => {
  if (reason === 'division by zero') return '.error .divisionByZero'
  if (reason === 'overflow') return '.error .overflow'
  if (reason === 'a out of bounds' || reason === 'b out of bounds') return '.error .invalidInput'
  throw new Error(`cannot serialize primitive failure: ${reason}`)
}
const resultLean = (result: PrimitiveResult): string => result.ok
  ? `.ok ${intLiteral(result.value)}` : errorLean(result.reason)

/** A closed obligation; Lean computes the result, not a custom arithmetic restatement.
 * `a`/`b` are strict exact decimal strings because specimens can cross JSON.
 * There is no write, check, toolchain invocation, or proof claim in this function.
 */
export function primitiveSpecimenObligation(
  spec: PrimitiveSpec, a: string, b?: string, name = 'integer_primitive_specimen',
): string {
  const left = decimal(a), right = b === undefined ? undefined : decimal(b)
  const result = evaluatePrimitive(spec, left, right)
  const expected = resultLean(result)
  return `theorem ${identifier(name)} : IntegerPrimitives.evaluate (${primitiveSpecLean(spec)}) ${intLiteral(left)} ${right === undefined ? 'none' : `(some ${intLiteral(right)})`} = ${expected} := by decide
#print axioms ${identifier(name)}`
}

/** Symbolic native-typed Lean definition. Each input is Lean's actual UIntN/IntN;
 * arithmetic/division uses IntegerPrimitives' standard BitVec/Int operations.
 * This exports semantics, not a proof of the separate TypeScript limb lowering.
 */
export function primitiveFunctionLean(spec: PrimitiveSpec, name = 'integer_primitive'): string {
  const captured = evaluatePrimitiveReceipt(spec, 0n).spec
  if (!captured) throw new Error('invalid primitive spec')
  const native = `${captured.signed ? 'Int' : 'UInt'}${captured.width}`
  const binary = ['add', 'sub', 'mul', 'div', 'rem'].includes(captured.operation)
  const left = captured.signed ? 'a.toInt' : '(Int.ofNat a.toNat)'
  const right = binary ? `(some ${captured.signed ? 'b.toInt' : '(Int.ofNat b.toNat)'})` : 'none'
  const convert = captured.signed ? `${native}.ofInt z` : `${native}.ofNat z.toNat`
  return `def ${identifier(name)} (a : ${native})${binary ? ` (b : ${native})` : ''} : Except IntegerPrimitives.Failure ${native} :=\n  (IntegerPrimitives.evaluate (${primitiveSpecLean(captured)}) ${left} ${right}).map (fun z => ${convert})\n#print axioms ${identifier(name)}\n`
}

export function toLeanIntegerPrimitive(spec: PrimitiveSpec, name = 'integer_primitive'): string {
  return `import IntegerPrimitives\n\n${primitiveFunctionLean(spec, name)}`
}

/** Standalone Lean source for a closed native probe; import path expects lean-kernel on LEAN_PATH. */
export function primitiveSpecimenLean(
  spec: PrimitiveSpec, a: string, b?: string, name = 'integer_primitive_specimen',
): string {
  return `import IntegerPrimitives\n\n${primitiveSpecimenObligation(spec, a, b, name)}\n`
}
