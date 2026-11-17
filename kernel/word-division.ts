// Trusted exact-word division facts. The reserved maps are computed by wordDivisionValue;
// callers must reject declarations which could shadow them.
import type {C, E} from '../core/machine.ts'

export type WordDivisionSpec = {width: 8 | 16 | 32 | 64, part: 'q' | 'r' | 'c', index: number}

export function wordDivisionName(width: WordDivisionSpec['width'], part: WordDivisionSpec['part'], index: number): string {
  if (![8, 16, 32, 64].includes(width) || !['q', 'r', 'c'].includes(part) || !Number.isSafeInteger(index) ||
      index < (part === 'c' ? 1 : 0) || index > (part === 'c' ? 2 * (width === 8 ? 1 : width / 16) : (width === 8 ? 1 : width / 16) - 1))
    throw new Error('invalid word division name')
  return `worddiv$${width}$${part}$${index}`
}

export function parseWordDivisionName(name: string): WordDivisionSpec | undefined {
  if (typeof name !== 'string') return undefined
  const m = /^worddiv\$(8|16|32|64)\$(q|r|c)\$(0|[1-9][0-9]*)$/.exec(name)
  if (!m) return undefined
  const width = Number(m[1]) as WordDivisionSpec['width']
  const part = m[2] as WordDivisionSpec['part']
  const index = Number(m[3])
  const n = width === 8 ? 1 : width / 16
  return Number.isSafeInteger(index) && (part === 'c' ? index >= 1 && index <= 2 * n : index < n)
    ? {width, part, index} : undefined
}

export function wordDivisionKey(args: E[]): E {
  if (args.length < 2) throw new Error('word division key needs at least two arguments')
  return args.slice(0, -1).reduceRight<E>((b, a) => ({op: 'tup', a, b}), args[args.length - 1]!)
}

export function wordDivisionArgs(key: E, width: WordDivisionSpec['width']): E[] | undefined {
  if (![8, 16, 32, 64].includes(width)) return undefined
  const count = 2 * (width === 8 ? 1 : width / 16)
  const args: E[] = []
  let node: E = key
  for (let i = 1; i < count; i++) {
    if (node.op !== 'tup') return undefined
    args.push(node.a)
    node = node.b
  }
  if (node.op === 'tup') return undefined
  args.push(node)
  return args
}

// Deliberately self-contained: compiled JavaScript embeds this function's source.
// Inputs are safe natural Numbers; every arithmetic step on word data is BigInt.
export function wordDivisionValue(width: 8 | 16 | 32 | 64, part: 'q' | 'r' | 'c', index: number, values: number[]): number {
  if (width !== 8 && width !== 16 && width !== 32 && width !== 64) throw new Error('invalid word division width')
  const n = width === 8 ? 1 : width / 16
  if (part !== 'q' && part !== 'r' && part !== 'c') throw new Error('invalid word division part')
  if (!Number.isSafeInteger(index) || (part === 'c' ? index < 1 || index > 2 * n : index < 0 || index >= n))
    throw new Error('invalid word division index')
  if (!Array.isArray(values) || values.length !== 2 * n) throw new Error('invalid word division arity')
  const base = width === 8 ? 256n : 65536n
  const digits: bigint[] = []
  for (const value of values) {
    if (!Number.isSafeInteger(value) || value < 0) throw new Error('invalid word division operand')
    digits.push(BigInt(value) % base)
  }
  let a = 0n, b = 0n, power = 1n
  for (let i = 0; i < n; i++) {
    a += digits[i]! * power
    b += digits[n + i]! * power
    power *= base
  }
  const q = b === 0n ? 0n : a / b
  const r = b === 0n ? 0n : a % b
  if (part === 'q' || part === 'r') return Number(((part === 'q' ? q : r) / (base ** BigInt(index))) % base)
  let carry = 0n
  for (let col = 0; col < index; col++) {
    let total = carry + (col < n ? (r / (base ** BigInt(col))) % base : 0n)
    for (let j = 0; j < n; j++) {
      const k = col - j
      if (k >= 0 && k < n) total += ((q / (base ** BigInt(j))) % base) * digits[n + k]!
    }
    carry = total / base
  }
  return Number(carry)
}

export function wordDivisionFacts(terms: unknown[]): C[] {
  const out: C[] = []
  const seen = new Set<object>()
  const keys = new Set<string>()
  const constant = (value: number): E => ({op: 'const', value})
  const add = (xs: E[]): E => xs.reduce((a, b) => ({op: 'add', a, b}), constant(0))
  const eq = (a: E, b: E): C => ({op: '=', a, b})
  const lt = (a: E, b: E): C => ({op: '<', a, b})
  const le = (a: E, b: E): C => ({op: '<=', a, b})
  const both = (xs: C[]): C => ({op: 'and', xs})
  const either = (xs: C[]): C => ({op: 'or', xs})
  const digitLex = (a: E[], b: E[], strict: boolean): C => {
    const alternatives: C[] = []
    for (let i = a.length - 1; i >= 0; i--)
      alternatives.push(both([...a.slice(i + 1).map((x, j) => eq(x, b[i + 1 + j]!)), lt(a[i]!, b[i]!)]))
    if (!strict) alternatives.push(both(a.map((x, i) => eq(x, b[i]!))))
    return either(alternatives)
  }
  const visit = (value: unknown): void => {
    if (!value || typeof value !== 'object' || seen.has(value)) return
    seen.add(value)
    if (!Array.isArray(value)) {
      const node = value as Record<string, unknown>
      if (node.op === 'get' && typeof node.map === 'string') {
        const spec = parseWordDivisionName(node.map)
        if (spec && node.key && typeof node.key === 'object') {
          const key = node.key as E
          const args = wordDivisionArgs(key, spec.width)
          if (args) {
            const tag = `${spec.width}:${JSON.stringify(key)}`
            if (!keys.has(tag)) {
              keys.add(tag)
              const n = spec.width === 8 ? 1 : spec.width / 16, base = spec.width === 8 ? 256 : 65536
              const a = args.slice(0, n), b = args.slice(n)
              const get = (part: WordDivisionSpec['part'], i: number): E => ({op: 'get', map: wordDivisionName(spec.width, part, i), key})
              const q = Array.from({length: n}, (_, i) => get('q', i))
              const r = Array.from({length: n}, (_, i) => get('r', i))
              const c = Array.from({length: 2 * n + 1}, (_, i) => i === 0 ? constant(0) : get('c', i))
              for (const x of [...q, ...r]) out.push(lt(x, constant(base)))
              for (let i = 1; i <= 2 * n; i++) out.push(le(c[i]!, constant(n * base)))
              const domain = both([...args.map(x => lt(x, constant(base))), either(b.map(x => lt(constant(0), x)))])
              const guarded = (fact: C): void => { out.push(either([{op: 'not', x: domain}, fact])) }
              for (let i = 0; i < 2 * n; i++) {
                const columns: E[] = [c[i]!]
                if (i < n) columns.push(r[i]!)
                for (let j = 0; j < n; j++) if (i - j >= 0 && i - j < n)
                  columns.push({op: 'prod', a: q[j]!, b: b[i - j]!})
                guarded(eq(add(columns), add([i < n ? a[i]! : constant(0), {op: 'mul', k: base, a: c[i + 1]!}])))
              }
              guarded(eq(c[2 * n]!, constant(0)))
              guarded(digitLex(r, b, true))
              guarded(digitLex(q, a, false))
              const bOne = both([eq(b[0]!, constant(1)), ...b.slice(1).map(x => eq(x, constant(0)))])
              guarded(either([{op: 'not', x: bOne}, both([...q.map((x, i) => eq(x, a[i]!)), ...r.map(x => eq(x, constant(0)))])]))
            }
          }
        }
      }
    }
    for (const child of Object.values(value)) visit(child)
  }
  visit(terms)
  return out
}
