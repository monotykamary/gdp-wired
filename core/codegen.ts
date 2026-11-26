// Shared expression, condition, and helper printer for BOTH `compileJsMode` (`core/machine.ts`) and standalone
// TypeScript source emission (`core/emit.ts`). Each caller supplies only its binding layer (slot-encoded runtime maps
// and safe-int `$x` checks in `core/machine.ts`; typed named fields, signed cancellation, and CSE in `core/emit.ts`).
import {type QC, type QE, unreachable} from '../kernel/kernel.ts'
import type {C, E, Machine} from './machine.ts'
import {DEC_ROUND_HELPER_LINES} from './decimal-round.ts'
import {q} from './q.ts'

// Compile-time exhaustive op and machine-part tables: adding any new AST op or Machine field fails `tsc` here until
// the shared printer and `core/emit.ts` handle it.
const E_OP_TABLE: Record<E['op'], true> = {
  var: true, const: true, add: true, sub: true, mul: true, prod: true,
  min: true, max: true, if: true, get: true, tup: true, proj: true,
}
const C_OP_TABLE: Record<C['op'], true> = {
  '<': true, '<=': true, '=': true, and: true, or: true, not: true, flag: true, all: true,
}
const QE_OP_TABLE: Record<QE['op'], true> = {
  var: true, const: true, add: true, sub: true, mul: true, min: true, max: true, if: true,
}
const QC_OP_TABLE: Record<QC['op'], true> = {
  '<=': true, '<': true, '=': true, and: true, or: true, not: true,
}
const MACHINE_PART_TABLE: Record<keyof Machine, true> = {
  name: true, params: true, inputs: true, state: true, maps: true, inputMaps: true,
  step: true, pre: true, assume: true, primitiveFailure: true, history: true,
  sums: true, counts: true, leasts: true, fns: true, facts: true, relations: true,
}
export const E_OPS = Object.keys(E_OP_TABLE) as readonly E['op'][]
export const C_OPS = Object.keys(C_OP_TABLE) as readonly C['op'][]
export const QE_OPS = Object.keys(QE_OP_TABLE) as readonly QE['op'][]
export const QC_OPS = Object.keys(QC_OP_TABLE) as readonly QC['op'][]
export const MACHINE_PARTS = Object.keys(MACHINE_PART_TABLE) as readonly (keyof Machine)[]

export type ExprHooks = {
  readonly onVar: (name: string) => string
  readonly onGet: (map: string, key: E, printE: (e: E) => string) => string
  readonly onFlag: (name: string) => string
  readonly onAll: (c: Extract<C, {op: 'all'}>, printE: (e: E) => string, printC: (c: C) => string) => string
  readonly wrapArith?: (expr: string) => string
  readonly onPair?: (a: string, b: string) => string
  readonly onProj?: (a: string, k: 0 | 1) => string
  readonly preExpr?: (e: E) => string | undefined
  readonly onAdd?: (a: E, b: E, printE: (e: E) => string) => string
  readonly simplifyMul?: boolean
  readonly onCmp?: (op: '<' | '<=' | '=', a: E, b: E, negated: boolean, printE: (e: E) => string) => string
  readonly onNot?: (x: C, printC: (c: C) => string) => string
  readonly simplifyBool?: boolean
}

export function createPrinter(hooks: ExprHooks): {printE: (e: E) => string, printC: (c: C) => string} {
  const wrap = hooks.wrapArith ?? ((expr: string) => `(${expr})`)

  const printE = (e: E): string => {
    const pre = hooks.preExpr?.(e)
    if (pre !== undefined) return pre
    switch (e.op) {
      case 'const': return String(e.value)
      case 'var': return hooks.onVar(e.name)
      case 'add': return hooks.onAdd ? hooks.onAdd(e.a, e.b, printE) : wrap(`${printE(e.a)} + ${printE(e.b)}`)
      case 'sub': return `Math.max(0, ${printE(e.a)} - ${printE(e.b)})`
      case 'mul':
        if (hooks.simplifyMul) {
          if (e.k === 0) return '0'
          if (e.k === 1) return printE(e.a)
        }
        return wrap(`${e.k} * ${printE(e.a)}`)
      case 'prod': return wrap(`${printE(e.a)} * ${printE(e.b)}`)
      case 'min': return `Math.min(${printE(e.a)}, ${printE(e.b)})`
      case 'max': return `Math.max(${printE(e.a)}, ${printE(e.b)})`
      case 'if': return `(${printC(e.c)} ? ${printE(e.then)} : ${printE(e.else)})`
      case 'tup': return hooks.onPair ? hooks.onPair(printE(e.a), printE(e.b)) : `$p(${printE(e.a)}, ${printE(e.b)})`
      case 'proj': return hooks.onProj ? hooks.onProj(printE(e.a), e.k) : `$u(${printE(e.a)})[${e.k}]`
      case 'get': return hooks.onGet(e.map, e.key, printE)
      default: return unreachable(e)
    }
  }

  const printC = (c: C): string => {
    switch (c.op) {
      case '<':
      case '<=':
      case '=':
        return hooks.onCmp
          ? hooks.onCmp(c.op, c.a, c.b, false, printE)
          : `(${printE(c.a)} ${c.op === '=' ? '===' : c.op} ${printE(c.b)})`
      case 'and': {
        if (!hooks.simplifyBool) return c.xs.length ? `(${c.xs.map(printC).join(' && ')})` : 'true'
        const parts: string[] = []
        for (const x of c.xs) {
          const s = printC(x)
          if (s === 'false') return 'false'
          if (s !== 'true' && !parts.includes(s)) parts.push(s)
        }
        return parts.length === 0 ? 'true' : parts.length === 1 ? parts[0]! : `(${parts.join(' && ')})`
      }
      case 'or': {
        if (!hooks.simplifyBool) return c.xs.length ? `(${c.xs.map(printC).join(' || ')})` : 'false'
        const parts: string[] = []
        for (const x of c.xs) {
          const s = printC(x)
          if (s === 'true') return 'true'
          if (s !== 'false' && !parts.includes(s)) parts.push(s)
        }
        return parts.length === 0 ? 'false' : parts.length === 1 ? parts[0]! : `(${parts.join(' || ')})`
      }
      case 'not':
        return hooks.onNot ? hooks.onNot(c.x, printC) : `(!${printC(c.x)})`
      case 'flag': return hooks.onFlag(c.name)
      case 'all': return hooks.onAll(c, printE, printC)
      default: return unreachable(c)
    }
  }

  return {printE, printC}
}

export type QExprHooks = {
  readonly onVar: (name: string) => string
  readonly add: (a: string, b: string) => string
  readonly sub: (a: string, b: string) => string
  readonly mul: (kLit: string, a: string) => string
  readonly min: (a: string, b: string) => string
  readonly max: (a: string, b: string) => string
  readonly cmp: (a: string, b: string) => string
  readonly onNot?: (inner: string) => string
}

// Shared rational expression/condition printer for BOTH `compileQJs` (`core/rationals.ts`) and `emitRatRule` (`core/emit.ts`).
export function createQPrinter(hooks: QExprHooks): {printQE: (t: QE) => string, printQC: (t: QC) => string} {
  const lit = (num: bigint, den: bigint): string => {
    const r = q(num, den)
    return `[${r.num}n, ${r.den}n]`
  }
  const printQE = (t: QE): string => {
    switch (t.op) {
      case 'var': return hooks.onVar(t.name)
      case 'const': return lit(t.q.num, t.q.den)
      case 'add': return hooks.add(printQE(t.a), printQE(t.b))
      case 'sub': return hooks.sub(printQE(t.a), printQE(t.b))
      case 'mul': return hooks.mul(lit(t.k.num, t.k.den), printQE(t.a))
      case 'min': return hooks.min(printQE(t.a), printQE(t.b))
      case 'max': return hooks.max(printQE(t.a), printQE(t.b))
      case 'if': return `(${printQC(t.c)} ? ${printQE(t.then)} : ${printQE(t.else)})`
      default: return unreachable(t)
    }
  }
  const printQC = (t: QC): string => {
    switch (t.op) {
      case '<=': return `(${hooks.cmp(printQE(t.a), printQE(t.b))} <= 0)`
      case '<': return `(${hooks.cmp(printQE(t.a), printQE(t.b))} < 0)`
      case '=': return `(${hooks.cmp(printQE(t.a), printQE(t.b))} === 0)`
      case 'and': return `(${printQC(t.a)} && ${printQC(t.b)})`
      case 'or': return `(${printQC(t.a)} || ${printQC(t.b)})`
      case 'not': return hooks.onNot ? hooks.onNot(printQC(t.x)) : `!${printQC(t.x)}`
      default: return unreachable(t)
    }
  }
  return {printQE, printQC}
}

// --- Shared runtime helpers (Cantor pair/unpair, compiled JS runtime, typed TS helpers) ------------------------------

const CANTOR_TRI = (v: string) => `(${v} % 2 === 0 ? (${v} / 2) * (${v} + 1) : ${v} * ((${v} + 1) / 2))`

// The runtime's helpers for `compileJsMode`: a compiled module declares only the ones it calls (transitively).
export const JS_RUNTIME: [string, string][] = [
  ['$n', `function $n(v, what) { if (typeof v !== 'number' || !Number.isSafeInteger(v) || v < 0) throw new RangeError(what + ' must be a natural below 2^53, not ' + v); return v; }`],
  ['$x', `function $x(v) { if (v > 9007199254740991) throw new RangeError('a value passed 2^53 - 1, past which the proofs over the naturals no longer describe the run'); return v; }`],
  ['$p', `function $p(a, b) { const s = a + b, v = ${CANTOR_TRI('s')} + b; if (!Number.isSafeInteger(v)) throw new RangeError('a tuple key passed 2^53 - 1, past which the proofs over the naturals no longer describe the run'); return v; }`],
  ['$u', `function $u(z) { const tri = t => ${CANTOR_TRI('t')}; let s = Math.floor((Math.sqrt(8 * z + 1) - 1) / 2); while (s > 0 && tri(s) > z) s--; while (tri(s + 1) <= z) s++; const b = z - tri(s); return [s - b, b]; }`],
  ['$m', `function $m(v, what) { if (!(v instanceof Map)) throw new RangeError(what + ' must be a Map of naturals'); for (const [key, x] of v) { $n(key, 'a key of ' + what); $n(x, 'a cell of ' + what); } return v; }`],
  // ($unique: the naturals of `vals` (each at most `top`) sorted and made unique. A dense range is marked in a reused
  // stamp buffer and read back in key order, no sort and no Set per step; a sparse one falls back to a Set and a sort.
  // The stamp never reaches 2^32 − 1: at that count the buffer is zeroed and the stamps restart at 1, so a stale mark
  // can never equal a live stamp; a grown buffer starts at 0 likewise.)
  ['$unique', `function $unique(vals, top) { if (top > 4 * vals.length + 64 || top > 1048576) return [...new Set(vals)].sort((a, b) => a - b); let buf = $unique.buf; if (!buf || buf.length <= top) { buf = new Uint32Array(Math.max(top + 1, buf ? 2 * buf.length : 256)); $unique.buf = buf; $unique.stamp = 0; } let s = $unique.stamp + 1; if (s >= 0xFFFFFFFF) { buf.fill(0); s = 1; } $unique.stamp = s; for (let i = 0; i < vals.length; i++) buf[vals[i]] = s; const out = []; for (let i = 0; i <= top; i++) if (buf[i] === s) out.push(i); return out; }`],
  ['$keys', `function $keys(maps, names) { const keys = []; let past = 0; for (const n of Object.keys(maps)) for (const key of maps[n].keys()) if (key + 1 > past) past = key + 1; for (const n of names) for (const key of maps[n].keys()) keys.push(key); const out = $unique(keys, past); out.push(past); return out; }`],
  // ($breaks: every breakpoint q of the reads and comparisons and its neighbours q − 1 .. q + 2, sorted and unique, then one
  // past the last. A dense set is marked straight into $unique's stamp buffer (no array of the neighbours and no second
  // pass); a sparse one goes through $unique's Set path. Both give the same list.)
  ['$breaks', `function $breaks(maps, reads, cmps) { const p = [0]; let top = 0; for (const [n, d, minus] of reads) { for (const s of maps[n].keys()) { const q = minus ? s + d : s - d; if (q >= 0) { p.push(q); if (q > top) top = q; } } if (minus) { p.push(d); if (d > top) top = d; } } for (const [v, d, minus] of cmps) { if (minus) { p.push(v + d); p.push(d); if (v + d > top) top = v + d; } else if (v >= d) { p.push(v - d); if (v - d > top) top = v - d; } } const t2 = top + 2; if (t2 > 16 * p.length + 64 || t2 > 1048576) { const vals = []; for (let j = 0; j < p.length; j++) { const q = p[j]; for (let i = -1; i <= 2; i++) if (q + i >= 0) vals.push(q + i); } const out = $unique(vals, t2); out.push(out[out.length - 1] + 1); return out; } let buf = $unique.buf; if (!buf || buf.length <= t2) { buf = new Uint32Array(Math.max(t2 + 1, buf ? 2 * buf.length : 256)); $unique.buf = buf; $unique.stamp = 0; } let s = $unique.stamp + 1; if (s >= 0xFFFFFFFF) { buf.fill(0); s = 1; } $unique.stamp = s; for (let j = 0; j < p.length; j++) { const q = p[j]; for (let i = q > 0 ? q - 1 : 0; i <= q + 2; i++) buf[i] = s; } const out = []; for (let i = 0; i <= t2; i++) if (buf[i] === s) out.push(i); out.push(out[out.length - 1] + 1); return out; }`],
  // A condition at every two keys that holds wherever x(k) differs from y(k1): only the pairs whose values match are read.
  ['$join', `function $join(ks, x, y, f) { const by = new Map(); for (const k1 of ks) { const v = y(k1), l = by.get(v); if (l) l.push(k1); else by.set(v, [k1]); } return ks.every(k => { const l = by.get(x(k)); return l === undefined || l.every(k1 => f(k, k1)); }); }`],
  ['$spread', `function $spread(keys, n) { const vals = []; let top = 0; for (const k of keys) for (let i = 0; i < n; i++) { vals.push(k + i); if (k + i > top) top = k + i; } return $unique(vals, top); }`],
  // (the interpreter's writeEvery: each breakpoint, and each stretch between two at one key of it, filled only where it
  // holds other than the value past the last)
  ['$dense', `function $dense(keys, f) { const top = keys[keys.length - 1], d = f(top), cells = new Map(); for (let i = 0; i + 1 < keys.length; i++) { const key = keys[i], v = f(key); if (v !== d) cells.set(key, v); if (keys[i + 1] > key + 1) { const u = f(key + 1); if (u !== d) { if (keys[i + 1] - key > 1000000) throw new RangeError('a write at every key fills a stretch of more than a million keys (' + (key + 1) + ' to ' + (keys[i + 1] - 1) + ')'); for (let k2 = key + 1; k2 < keys[i + 1]; k2++) cells.set(k2, u); } } } return {cells, d}; }`],
  // (a request's count map in the generated code: each cell its sum, computed when first read, as carriedView's CountCells)
  ['$cells', `class $cells extends Map { constructor(at) { super(); this.at = at; } get(x) { let v = super.get(x); if (v === undefined) { v = this.at(x); super.set(x, v); } return v; } }`],
  ['$every', `function $every(keys, f) { const past = keys[keys.length - 1], d = f(past), cells = new Map(); for (let i = 0; i < keys.length - 1; i++) { const v = f(keys[i]); if (v !== d) cells.set(keys[i], v); } return {cells, d}; }`],
]

export function runtimeFor(code: string): string {
  const used = new Set<string>()
  for (let grew = true; grew;) {
    grew = false
    const text = code + JS_RUNTIME.filter(([name]) => used.has(name)).map(([, src]) => src).join('')
    for (const [name] of JS_RUNTIME) if (!used.has(name) && text.includes(`${name}(`)) { used.add(name); grew = true }
  }
  return JS_RUNTIME.filter(([name]) => used.has(name)).map(([, src]) => `${src}\n`).join('')
}

export type EmitHelper =
  | 'glob'
  | 'cpair'
  | 'cunpair'
  | 'dec'
  | 'decRound'
  | 'idx'
  | 'unique'
  | 'partsOf'
  | 'keys'
  | 'breaks'
  | 'join'
  | 'spread'
  | 'dense'
  | 'every'
  | 'everyTuple'
  | 'countCells'
  | 'wordDiv'
  | 'fixedLimbs'

// Typed standalone TS helpers emitted by `core/emit.ts` (sharing Cantor pair/unpair and half-even rounding sources).
export function renderTypedHelpers(rawHelpers: ReadonlySet<EmitHelper>): string[] {
  const helpers = new Set<EmitHelper>(rawHelpers)
  if (helpers.has('keys')) helpers.add('unique')
  if (helpers.has('breaks')) { helpers.add('unique'); helpers.add('partsOf') }
  if (helpers.has('spread')) helpers.add('unique')
  if (helpers.has('everyTuple')) helpers.add('cpair')
  if (helpers.has('partsOf')) helpers.add('cunpair')
  const out: string[] = []
  if (helpers.has('idx')) out.push('function $idx<T extends string>(v: T, xs: readonly T[]): number { const i = xs.indexOf(v); if (i < 0) throw new RangeError(`unexpected choice ${v}`); return i }')
  if (helpers.has('dec')) {
    out.push(
      'function $dec(x: number, places: number, scale: number, name: string): number {',
      '  if (!Number.isFinite(x)) throw new RangeError(`${name}: expected finite decimal`)',
      '  const text = x.toFixed(places + 3)',
      '  const m = /^(-?)(\\d+)(?:\\.(\\d+))?$/.exec(text)',
      '  if (!m) throw new RangeError(`${name}: invalid decimal ${x}`)',
      "  const frac = (m[3] ?? '').replace(/0+$/, '')",
      '  if (frac.length > places) throw new RangeError(`${name}: needs more than ${places} decimal places`)',
      "  const n = Number(m[2]) * scale + Number(frac.padEnd(places, '0') || '0')",
      '  if (!Number.isSafeInteger(n)) throw new RangeError(`${name}: decimal out of safe integer range`)',
      '  return m[1] && n !== 0 ? -n : n',
      '}',
    )
  }
  if (helpers.has('decRound')) {
    out.push(...DEC_ROUND_HELPER_LINES)
  }
  if (helpers.has('glob')) {
    out.push(
      'function $globMatch(pattern: string, text: string): boolean {',
      '  const parts: string[][] = [[]]',
      '  for (let i = 0; i < pattern.length; i++) {',
      "    if (pattern[i] === '\\\\' && pattern[i + 1] === '*') { parts[parts.length - 1]!.push('*'); i++ }",
      "    else if (pattern[i] === '*') parts.push([])",
      '    else parts[parts.length - 1]!.push(pattern[i]!)',
      '  }',
      "  const lits = parts.map(p => p.join(''))",
      '  if (lits.length === 1) return text === lits[0]',
      '  const head = lits[0]!, tail = lits[lits.length - 1]!',
      '  if (!text.startsWith(head) || !text.endsWith(tail) || text.length < head.length + tail.length) return false',
      '  let at = head.length',
      '  const end = text.length - tail.length',
      '  for (const lit of lits.slice(1, -1)) {',
      '    const idx = text.indexOf(lit, at)',
      '    if (idx < 0 || idx + lit.length > end) return false',
      '    at = idx + lit.length',
      '  }',
      '  return true',
      '}',
    )
  }
  if (helpers.has('cpair')) {
    out.push(
      'function $cpair(a: number, b: number): number {',
      '  const s = a + b',
      `  const v = s % 2 === 0 ? (s / 2) * (s + 1) + b : s * ((s + 1) / 2) + b`,
      "  if (!Number.isSafeInteger(v)) throw new RangeError('tuple key passed safe integer range')",
      '  return v',
      '}',
    )
  }
  if (helpers.has('cunpair')) {
    out.push(
      'function $cunpair(z: number): readonly [number, number] {',
      `  const tri = (s: number) => ${CANTOR_TRI('s')}`,
      '  let s = Math.floor((Math.sqrt(8 * z + 1) - 1) / 2)',
      '  while (s > 0 && tri(s) > z) s--',
      '  while (tri(s + 1) <= z) s++',
      '  const b = z - tri(s)',
      '  return [s - b, b]',
      '}',
    )
  }
  if (helpers.has('partsOf')) {
    out.push(
      'function $partsOf(z: number, n: number): number[] {',
      '  const out: number[] = []',
      '  let cur = z',
      '  for (let i = 0; i + 1 < n; i++) { const [a, b] = $cunpair(cur); out.push(a); cur = b }',
      '  out.push(cur)',
      '  return out',
      '}',
    )
  }
  if (helpers.has('unique')) {
    out.push(
      'function $unique(vals: readonly number[], top: number): number[] {',
      '  if (top > 4 * vals.length + 64 || top > 1048576) return [...new Set(vals)].sort((a, b) => a - b)',
      '  const seen = new Uint8Array(top + 1)',
      '  for (let i = 0; i < vals.length; i++) seen[vals[i]!] = 1',
      '  const out: number[] = []',
      '  for (let i = 0; i <= top; i++) if (seen[i]) out.push(i)',
      '  return out',
      '}',
    )
  }
  if (helpers.has('keys')) {
    out.push(
      'function $keys(maps: Record<string, ReadonlyMap<number, unknown>>, names: readonly string[]): number[] {',
      '  const keys: number[] = []',
      '  let past = 0',
      '  for (const m of Object.values(maps)) for (const key of m.keys()) if (key + 1 > past) past = key + 1',
      '  for (const n of names) { const m = maps[n]; if (m) for (const key of m.keys()) keys.push(key) }',
      '  const out = $unique(keys, past)',
      '  out.push(past)',
      '  return out',
      '}',
    )
  }
  if (helpers.has('breaks')) {
    out.push(
      'function $breaks(',
      '  maps: Record<string, ReadonlyMap<number, unknown>>,',
      '  reads: readonly (readonly [string, number, boolean, (readonly [number, number])?])[],',
      '  cmps: readonly (readonly [number, number, boolean])[],',
      '): number[] {',
      '  const p: number[] = [0]',
      '  let top = 0',
      '  for (const [n, d, minus, part] of reads) {',
      '    const m = maps[n]',
      '    if (m) {',
      '      for (const s0 of m.keys()) {',
      '        const s = part ? $partsOf(s0, part[1])[part[0]]! : s0',
      '        const q = minus ? s + d : s - d',
      '        if (q >= 0) { p.push(q); if (q > top) top = q }',
      '      }',
      '    }',
      '    if (minus) { p.push(d); if (d > top) top = d }',
      '  }',
      '  for (const [v, d, minus] of cmps) {',
      '    if (minus) { p.push(v + d, d); if (v + d > top) top = v + d }',
      '    else if (v >= d) { p.push(v - d); if (v - d > top) top = v - d }',
      '  }',
      '  const vals: number[] = []',
      '  for (let j = 0; j < p.length; j++) {',
      '    const q = p[j]!',
      '    for (let i = -1; i <= 2; i++) if (q + i >= 0) vals.push(q + i)',
      '  }',
      '  const out = $unique(vals, top + 2)',
      '  out.push(out[out.length - 1]! + 1)',
      '  return out',
      '}',
    )
  }
  if (helpers.has('join')) {
    out.push(
      'function $join(ks: readonly number[], x: (k: number) => number, y: (k1: number) => number, f: (k: number, k1: number) => boolean): boolean {',
      '  const by = new Map<number, number[]>()',
      '  for (const k1 of ks) { const v = y(k1); const l = by.get(v); if (l) l.push(k1); else by.set(v, [k1]) }',
      '  return ks.every(k => { const l = by.get(x(k)); return l === undefined || l.every(k1 => f(k, k1)) })',
      '}',
    )
  }
  if (helpers.has('spread')) {
    out.push(
      'function $spread(keys: readonly number[], n: number): number[] {',
      '  const vals: number[] = []',
      '  let top = 0',
      '  for (const k of keys) for (let i = 0; i < n; i++) { vals.push(k + i); if (k + i > top) top = k + i }',
      '  return $unique(vals, top)',
      '}',
    )
  }
  if (helpers.has('dense')) {
    out.push(
      'function $dense<T>(keys: readonly number[], f: (k: number) => T, eq: (a: T, b: T) => boolean = (a, b) => a === b): { readonly cells: Map<number, T>; readonly d: T } {',
      '  const top = keys[keys.length - 1]!, d = f(top), cells = new Map<number, T>()',
      '  for (let i = 0; i + 1 < keys.length; i++) {',
      '    const key = keys[i]!, v = f(key)',
      '    if (!eq(v, d)) cells.set(key, v)',
      '    if (keys[i + 1]! > key + 1) {',
      '      const u = f(key + 1)',
      '      if (!eq(u, d)) {',
      "        if (keys[i + 1]! - key > 1000000) throw new RangeError('a write at every key fills a stretch of more than a million keys')",
      '        for (let k2 = key + 1; k2 < keys[i + 1]!; k2++) cells.set(k2, u)',
      '      }',
      '    }',
      '  }',
      '  return { cells, d }',
      '}',
    )
  }
  if (helpers.has('every')) {
    out.push(
      'function $every<T>(keys: readonly number[], f: (k: number) => T, eq: (a: T, b: T) => boolean = (a, b) => a === b): { readonly cells: Map<number, T>; readonly d: T } {',
      '  const past = keys[keys.length - 1]!, d = f(past), cells = new Map<number, T>()',
      '  for (let i = 0; i < keys.length - 1; i++) { const v = f(keys[i]!); if (!eq(v, d)) cells.set(keys[i]!, v) }',
      '  return { cells, d }',
      '}',
    )
  }
  if (helpers.has('everyTuple')) {
    out.push(
      'function $everyTuple(kss: readonly (readonly number[])[], crossed: boolean, at: (xs: readonly number[]) => number): { readonly cells: Map<number, number>; readonly d: number } {',
      '  const n = kss.length',
      '  const fallback = at(kss.map(ks => ks[ks.length - 1]!))',
      '  const cells = new Map<number, number>()',
      '  const segss = kss.map(ks => {',
      '    const segs: (readonly [number, number])[] = []',
      '    for (let i = 0; i < ks.length; i++) {',
      '      segs.push([ks[i]!, i + 1 < ks.length ? ks[i]! + 1 : Infinity])',
      '      if (i + 1 < ks.length && ks[i + 1]! > ks[i]! + 1) segs.push([ks[i]! + 1, ks[i + 1]!])',
      '    }',
      '    return segs',
      '  })',
      '  const tupleKey = (xs: readonly number[]): number => xs.slice(0, -1).reduceRight((b, a) => $cpair(a, b), xs[xs.length - 1]!)',
      '  const go = (i: number, picked: (readonly [number, number])[]): void => {',
      '    if (i < n) { for (const g of segss[i]!) go(i + 1, [...picked, g]); return }',
      '    const v = at(picked.map(g => g[0]))',
      '    if (v === fallback) return',
      "    if (picked.some(g => g[1] === Infinity)) throw new RangeError('a write at every tuple holds other than its default at tuples without end')",
      '    const wide = picked.filter(g => g[1] - g[0] > 1).length',
      "    if (wide > 1 && crossed) throw new RangeError('a write at every tuple compares its parts along stretches of keys')",
      '    let size = 1',
      '    for (const g of picked) size *= g[1] - g[0]',
      "    if (size > 1000000) throw new RangeError('a write at every tuple fills more than a million tuples at once')",
      '    const fill = (j: number, xs: number[]): void => {',
      '      if (j === n) { cells.set(tupleKey(xs), v); return }',
      '      for (let x = picked[j]![0]; x < picked[j]![1]; x++) fill(j + 1, [...xs, x])',
      '    }',
      '    fill(0, [])',
      '  }',
      '  go(0, [])',
      '  return { cells, d: fallback }',
      '}',
    )
  }
  if (helpers.has('countCells')) {
    out.push(
      'class $CountCells extends Map<number, number> {',
      '  private readonly at: (x: number) => number',
      '  constructor(at: (x: number) => number) { super(); this.at = at }',
      '  override get(x: number): number {',
      '    let v = super.get(x)',
      '    if (v === undefined) { v = this.at(x); super.set(x, v) }',
      '    return v',
      '  }',
      '}',
    )
  }
  if (helpers.has('wordDiv')) {
    out.push(
      "function $wordDiv(width: 8 | 16 | 32 | 64, part: 'q' | 'r' | 'c', index: number, values: readonly number[]): number {",
      '  const n = width === 8 ? 1 : width / 16',
      '  const base = width === 8 ? 256n : 65536n',
      '  const digits: bigint[] = []',
      '  for (const val of values) {',
      "    if (!Number.isSafeInteger(val) || val < 0) throw new RangeError('invalid word division operand')",
      '    digits.push(BigInt(val) % base)',
      '  }',
      '  let a = 0n, b = 0n, power = 1n',
      '  for (let i = 0; i < n; i++) { a += digits[i]! * power; b += digits[n + i]! * power; power *= base }',
      '  const q = b === 0n ? 0n : a / b',
      '  const r = b === 0n ? 0n : a % b',
      "  if (part === 'q' || part === 'r') return Number(((part === 'q' ? q : r) / (base ** BigInt(index))) % base)",
      '  let carry = 0n',
      '  for (let col = 0; col < index; col++) {',
      '    let total = carry + (col < n ? (r / (base ** BigInt(col))) % base : 0n)',
      '    for (let j = 0; j < n; j++) {',
      '      const k = col - j',
      '      if (k >= 0 && k < n) total += ((q / (base ** BigInt(j))) % base) * digits[n + k]!',
      '    }',
      '    carry = total / base',
      '  }',
      '  return Number(carry)',
      '}',
    )
  }
  if (helpers.has('fixedLimbs')) {
    out.push(
      'function $fixedLimbs(raw: number | string, width: 8 | 16 | 32 | 64, signed: boolean, name: string): readonly number[] {',
      '  let v: bigint',
      "  if (typeof raw === 'number') { if (!Number.isSafeInteger(raw)) throw new RangeError(`${name}: expected integer`); v = BigInt(raw) }",
      "  else if (typeof raw === 'string' && /^-?\\d+$/.test(raw)) v = BigInt(raw)",
      '  else throw new RangeError(`${name}: invalid fixed-${width} value`)',
      '  const lo = signed ? -(1n << BigInt(width - 1)) : 0n',
      '  const hi = signed ? (1n << BigInt(width - 1)) - 1n : (1n << BigInt(width)) - 1n',
      "  if (v < lo || v > hi) throw new RangeError(`${name}: out of ${signed ? 'i' : 'u'}${width} range`)",
      '  let u = v < 0n ? v + (1n << BigInt(width)) : v',
      '  const n = width === 8 ? 1 : width / 16',
      '  const base = width === 8 ? 256n : 65536n',
      '  const out: number[] = []',
      '  for (let i = 0; i < n; i++) { out.push(Number(u % base)); u /= base }',
      '  return out',
      '}',
    )
  }
  return out
}
