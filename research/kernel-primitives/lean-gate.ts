// Finite closed-case gate, not a universal proof of the TypeScript evaluator.
// Usage: bun research/kernel-primitives/lean-gate.ts OUTPUT
//        bun research/kernel-primitives/lean-gate.ts --audit OUTPUT LEAN_LOG
// The caller compiles OUTPUT with Lean and captures LEAN_LOG; this program never
// invokes a compiler or treats source generation as a successful kernel check.
import {readFileSync, writeFileSync} from 'node:fs'
import {primitiveFunctionLean, primitiveSpecimenObligation} from '../../lean-kernel/integer-primitives.ts'
import {evaluatePrimitive} from '../../kernel/integer-primitives.ts'
import {auditLiftLog} from '../../lean-kernel/axiom-audit.ts'
import type {PrimitiveSpec, Width} from '../../kernel/integer-primitives.ts'

type Case = {s: PrimitiveSpec, a: bigint, b?: bigint}
const cases: Case[] = []
const add = (s: PrimitiveSpec, a: bigint, b?: bigint): void => { cases.push({s, a, b}) }
const widths: readonly Width[] = [8, 16, 32, 64]
for (const width of widths) for (const signed of [false, true]) {
  const half = 1n << BigInt(width - 1)
  const lo = signed ? -half : 0n
  const hi = signed ? half - 1n : 2n * half - 1n
  const spec = (operation: PrimitiveSpec['operation'], overflow: PrimitiveSpec['overflow'], division?: PrimitiveSpec['division']): PrimitiveSpec =>
    ({width, signed, operation, overflow, ...(division ? {division} : {})})
  for (const operation of ['add', 'sub'] as const) {
    add(spec(operation, 'WRAP'), hi, operation === 'sub' ? lo : hi)
    add(spec(operation, 'TRAP'), lo, operation === 'sub' ? hi : lo)
  }
  add(spec('mul', 'WRAP'), hi, hi)
  add(spec('add', 'SATURATE'), hi, hi)
  add(spec('neg', 'WRAP'), lo)
  add(spec('neg', 'TRAP'), lo)
  add(spec('cast', 'SATURATE'), -(2n ** 100n))
  add(spec('cast', 'WRAP'), 2n ** 100n + 123n)
  for (const operation of ['div', 'rem'] as const) {
    for (const division of (width === 8 ? ['FLOOR', 'TRUNCATING', 'EUCLIDEAN'] : ['EUCLIDEAN']) as PrimitiveSpec['division'][]) {
      // Distinguishes the modes for signed negative dividends; positive inputs
      // also cover unsigned divisions and exact normal results.
      add(spec(operation, 'WRAP', division), signed ? -7n : 7n, signed ? 3n : 3n)
      add(spec(operation, 'TRAP', division), signed ? lo : hi, 0n)
      if (signed) add(spec(operation, 'TRAP', division), lo, -1n)
    }
  }
  // Operand validation is independently checked, not silently normalized.
  add(spec('add', 'WRAP'), hi + 1n, 1n)
}
if (cases.length > 150) throw new Error('case budget exceeded')
const names = cases.map((_, i) => 'integer_gate_' + String(i).padStart(3, '0'))
const bridgeClaims = [
  'FixedLimbBridge.digit_carry', 'FixedLimbBridge.addCarry_reconstruct',
  'FixedLimbBridge.addCarry_digits', 'FixedLimbBridge.assemble_bound',
  'FixedLimbBridge.addCarry_wrap', 'FixedLimbBridge.one_limb_add_wrap',
  'FixedLimbBridge.two_limb_add_wrap', 'FixedLimbBridge.four_limb_add_wrap',
]
const nativeNames: string[] = [], nativeSources: string[] = []
for (const width of widths) for (const signed of [false, true]) for (const operation of ['add', 'div'] as const) {
  const spec: PrimitiveSpec = {width, signed, operation, overflow: operation === 'div' ? 'TRAP' : 'WRAP', ...(operation === 'div' ? {division: 'TRUNCATING' as const} : {})}
  const id = `native_${signed ? 'i' : 'u'}${width}_${operation}`
  const theorem = `${id}_example`, native = `${signed ? 'Int' : 'UInt'}${width}`
  const literal = (n: bigint) => signed ? `(${native}.ofInt (${n}))` : `(${native}.ofNat ${n})`
  const half = 1n << BigInt(width - 1), max = signed ? half - 1n : half * 2n - 1n
  const a = operation === 'div' && signed ? -half : max, b = operation === 'div' ? signed ? -1n : 0n : 1n
  const result = evaluatePrimitive(spec, a, b)
  const expected = result.ok ? `.ok ${literal(result.value)}` : `.error .${result.reason === 'division by zero' ? 'divisionByZero' : 'overflow'}`
  nativeNames.push(id, theorem)
  nativeSources.push(primitiveFunctionLean(spec, id), `theorem ${theorem} : ${id} ${literal(a)} ${literal(b)} = ${expected} := by decide\n#print axioms ${theorem}\n`)
}

const source = 'import IntegerPrimitives\nimport FixedLimbBridge\n\n' + cases.map(({s, a, b}, i) =>
  primitiveSpecimenObligation(s, a.toString(), b?.toString(), names[i])).join('\n\n') +
  '\n\n' + nativeSources.join('\n') + '\n' + bridgeClaims.map(n => `#print axioms ${n}`).join('\n') + '\n'
const args = process.argv.slice(2)
if (args.length === 1 && args[0] !== '--audit') {
  writeFileSync(args[0]!, source)
  console.log(JSON.stringify({output: args[0], claims: names.length, axiomQuestions: names.length + 8 + nativeNames.length,
    note: 'unverified source: compile with Lean and audit its complete log'}))
} else if (args.length === 3 && args[0] === '--audit') {
  const generated = readFileSync(args[1]!, 'utf8')
  if (generated !== source) throw new Error('generated source differs from this deterministic gate')
  const log = readFileSync(args[2]!, 'utf8')
  if (/\berror:|declaration uses 'sorry'/.test(log)) throw new Error('Lean reported error or sorry')
  const required = [...bridgeClaims, ...names, ...nativeNames]
  const rows = auditLiftLog(log, [generated], required)
  console.log(JSON.stringify({checked: rows.length, strictStandardAxioms: true}))
} else throw new Error('usage: lean-gate.ts OUTPUT | --audit OUTPUT LEAN_LOG')
