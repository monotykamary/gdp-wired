// Emit self-contained, zero-dependency TypeScript source from proven gdp-wired rules, functions, rational rules and
// statecharts. Generated code has zero imports, zero dynamic code generation, and zero proof/kernel runtime.
// Header comments record the rule name, version, canonical machine digest, exact arithmetic semantics, and every
// law's proof status. Differential verification (`gdp-wired emit --verify`) tests the emitted module directly against
// the proven rule's interpreter on exhaustive small domains and randomized runs.
import type {QMachine, QC, QE, QLaw, StepLaw} from '../kernel/kernel.ts'
import {type C, type DirectFn, type E, type Fn, type Law, type Machine, directOf, pairedArgs} from './machine.ts'
import {
  type Decision,
  type Fun,
  type KindInfo,
  type ProveOptions,
  type Raw,
  type Rule,
  type RuleMeta,
  type Verdict,
  Unproven,
  funOf,
  inspectFunMeta,
  inspectRuleMeta,
  interned,
  proveDecision,
  proveRule,
  proveSteps,
} from './dsl.ts'
import {type RatLaw, type RatRule, inspectRatRule, proveRatRule} from './rationals.ts'
import {type Chart, inspectChart} from './chart.ts'
import {DEC_ROUND_HELPER_LINES} from './decimal-round.ts'
import {q} from './q.ts'

export const GDP_WIRED_VERSION = '0.61.0'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyRule = Rule<any, any, any, any, any, any, any, any>
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyFun = Fun<any, any, any>
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyRatRule = RatRule<any, any, any>
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyChart = Chart<any, any, any>

export type EmitLawReport = {
  readonly name: string
  readonly kind: 'law' | 'step' | 'decision'
  readonly proven: boolean
  readonly checked: boolean
  readonly assumes?: readonly string[]
  readonly goal?: string
  readonly why?: string
}

export type EmitResult = {
  readonly source: string
  readonly digest: string
  readonly version: string
  readonly name: string
  readonly kind: 'rule' | 'fun' | 'ratRule' | 'chart'
  readonly exportName: string
  readonly laws: readonly EmitLawReport[]
  readonly allProven: boolean
}

export type EmitProvenance = {
  readonly model: string
  readonly out?: string
}

export type EmitRuleOptions = {
  laws?: readonly Law[]
  stepLaws?: readonly StepLaw[]
  name?: string
  from?: 'any'
  ms?: number
  prove?: ProveOptions
  allowUnproven?: boolean
  provenance?: EmitProvenance
}

export type EmitFunOptions = {
  laws?: readonly Decision[]
  name?: string
  defaultParams?: Readonly<Record<string, Raw>>
  ms?: number
  allowUnproven?: boolean
  provenance?: EmitProvenance
}

export type EmitRatOptions = {
  laws?: readonly RatLaw<string, string>[]
  name?: string
  ms?: number
  depth?: number
  allowUnproven?: boolean
  provenance?: EmitProvenance
}

export type EmitChartOptions = {
  laws?: readonly Law[]
  stepLaws?: readonly StepLaw[]
  name?: string
  from?: 'any'
  ms?: number
  prove?: ProveOptions
  allowUnproven?: boolean
  provenance?: EmitProvenance
}

export type EmitBundle =
  | {readonly rule: AnyRule, readonly laws?: readonly Law[], readonly stepLaws?: readonly StepLaw[], readonly name?: string, readonly from?: 'any', readonly ms?: number}
  | {readonly fun: AnyFun, readonly laws?: readonly Decision[], readonly name?: string, readonly defaultParams?: Readonly<Record<string, Raw>>, readonly ms?: number}
  | {readonly ratRule: AnyRatRule, readonly laws?: readonly RatLaw<string, string>[], readonly name?: string, readonly ms?: number}
  | {readonly chart: AnyChart, readonly laws?: readonly Law[], readonly stepLaws?: readonly StepLaw[], readonly name?: string, readonly from?: 'any', readonly ms?: number}

// --- Pure-JS SHA-256 & canonical machine digest ----------------------------------------------------------------------

const SHA256_K = [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
] as const

export function sha256Hex(text: string): string {
  const bytes = new TextEncoder().encode(text)
  const bitLen = bytes.length * 8
  const padLen = ((bytes.length + 9 + 63) >> 6) << 6
  const buf = new Uint8Array(padLen)
  buf.set(bytes)
  buf[bytes.length] = 0x80
  const view = new DataView(buf.buffer)
  view.setUint32(padLen - 8, Math.floor(bitLen / 0x100000000), false)
  view.setUint32(padLen - 4, bitLen >>> 0, false)
  let h0 = 0x6a09e667, h1 = 0xbb67ae85, h2 = 0x3c6ef372, h3 = 0xa54ff53a
  let h4 = 0x510e527f, h5 = 0x9b05688c, h6 = 0x1f83d9ab, h7 = 0x5be0cd19
  const w = new Uint32Array(64)
  const rotr = (x: number, n: number) => (x >>> n) | (x << (32 - n))
  for (let off = 0; off < padLen; off += 64) {
    for (let i = 0; i < 16; i++) w[i] = view.getUint32(off + i * 4, false)
    for (let i = 16; i < 64; i++) {
      const s0 = rotr(w[i - 15]!, 7) ^ rotr(w[i - 15]!, 18) ^ (w[i - 15]! >>> 3)
      const s1 = rotr(w[i - 2]!, 17) ^ rotr(w[i - 2]!, 19) ^ (w[i - 2]! >>> 10)
      w[i] = (w[i - 16]! + s0 + w[i - 7]! + s1) >>> 0
    }
    let a = h0, b = h1, c = h2, d = h3, e = h4, f = h5, g = h6, h = h7
    for (let i = 0; i < 64; i++) {
      const S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)
      const ch = (e & f) ^ (~e & g)
      const t1 = (h + S1 + ch + SHA256_K[i]! + w[i]!) >>> 0
      const S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)
      const maj = (a & b) ^ (a & c) ^ (b & c)
      const t2 = (S0 + maj) >>> 0
      h = g; g = f; f = e; e = (d + t1) >>> 0; d = c; c = b; b = a; a = (t1 + t2) >>> 0
    }
    h0 = (h0 + a) >>> 0; h1 = (h1 + b) >>> 0; h2 = (h2 + c) >>> 0; h3 = (h3 + d) >>> 0
    h4 = (h4 + e) >>> 0; h5 = (h5 + f) >>> 0; h6 = (h6 + g) >>> 0; h7 = (h7 + h) >>> 0
  }
  return [h0, h1, h2, h3, h4, h5, h6, h7].map(x => x.toString(16).padStart(8, '0')).join('')
}

function canonicalJson(v: unknown): string {
  if (v === null || typeof v === 'boolean' || typeof v === 'string') return JSON.stringify(v)
  if (typeof v === 'number') return Object.is(v, -0) ? '0' : JSON.stringify(v)
  if (typeof v === 'bigint') return JSON.stringify({$bigint: v.toString()})
  if (Array.isArray(v)) return `[${v.map(x => (x === undefined ? 'null' : canonicalJson(x))).join(',')}]`
  if (typeof v === 'object') {
    const keys = Object.keys(v as Record<string, unknown>).filter(k => (v as Record<string, unknown>)[k] !== undefined).sort()
    return `{${keys.map(k => `${JSON.stringify(k)}:${canonicalJson((v as Record<string, unknown>)[k])}`).join(',')}}`
  }
  return 'null'
}

function stripFnMeta(fn: Fn): unknown {
  const direct = directOf(fn)
  return {
    js: fn.js,
    arity: fn.arity ?? 1,
    ...(fn.call ? {call: fn.call} : {}),
    ...(direct ? {direct: direct.kind === 'recur' ? {kind: 'recur', name: direct.name, args: direct.args, zero: direct.zero, next: direct.next, uses: Object.fromEntries(Object.entries(direct.uses).map(([k, u]) => [k, stripFnMeta(u)]))} : {kind: direct.kind, ...('divisor' in direct ? {divisor: direct.divisor} : {value: direct.value})}} : {}),
  }
}

export function machineDigest(m: Machine): string {
  const norm = {
    name: m.name,
    params: m.params,
    inputs: m.inputs,
    state: m.state,
    ...(m.maps ? {maps: m.maps} : {}),
    ...(m.inputMaps ? {inputMaps: m.inputMaps} : {}),
    step: m.step,
    ...(m.pre ? {pre: m.pre} : {}),
    ...(m.assume ? {assume: m.assume} : {}),
    ...(m.primitiveFailure ? {primitiveFailure: m.primitiveFailure} : {}),
    ...(m.history ? {history: m.history} : {}),
    ...(m.sums ? {sums: m.sums} : {}),
    ...(m.counts ? {counts: m.counts} : {}),
    ...(m.leasts ? {leasts: m.leasts} : {}),
    ...(m.fns ? {fns: Object.fromEntries(Object.entries(m.fns).map(([k, f]) => [k, stripFnMeta(f)]))} : {}),
  }
  return `sha256:${sha256Hex(canonicalJson(norm))}`
}

export function qMachineDigest(m: QMachine): string {
  return `sha256:${sha256Hex(canonicalJson(m))}`
}

// --- Identifier & formatting helpers ---------------------------------------------------------------------------------

const PLAIN_IDENT = /^[A-Za-z_][A-Za-z0-9_]*$/
const RESERVED_IDENT = new Set([
  'break', 'case', 'catch', 'class', 'const', 'continue', 'debugger', 'default', 'delete', 'do', 'else', 'enum',
  'export', 'extends', 'false', 'finally', 'for', 'function', 'if', 'implements', 'import', 'in', 'instanceof',
  'interface', 'let', 'new', 'null', 'package', 'private', 'protected', 'public', 'return', 'static', 'super',
  'switch', 'this', 'throw', 'true', 'try', 'typeof', 'var', 'void', 'while', 'with', 'yield', 'eval', 'arguments',
  'undefined', 'NaN', 'Infinity', 'Math', 'Number', 'Object', 'Array', 'Map', 'Set', 'String', 'Boolean', 'BigInt',
  'RangeError', 'TypeError', 'Error', 'Params', 'Input', 'State', 'Result', 'init', 'step', 'allowed', 'defaultParams',
])

function wordsOf(name: string): string[] {
  const raw = name.replace(/([a-z0-9])([A-Z])/g, '$1 $2').split(/[^A-Za-z0-9]+/).filter(Boolean)
  return raw.length ? raw : ['rule']
}

function toCamel(name: string): string {
  const ws = wordsOf(name)
  let id = ws.map((w, i) => (i === 0 ? w.charAt(0).toLowerCase() + w.slice(1) : w.charAt(0).toUpperCase() + w.slice(1))).join('')
  if (/^\d/.test(id)) id = `fn_${id}`
  if (RESERVED_IDENT.has(id)) id = `${id}Fn`
  return id
}

function propKey(k: string): string { return PLAIN_IDENT.test(k) ? k : JSON.stringify(k) }
function propAccess(base: string, k: string): string { return PLAIN_IDENT.test(k) ? `${base}.${k}` : `${base}[${JSON.stringify(k)}]` }
function safeVar(prefix: string, name: string): string { return `${prefix}${name.replace(/[^A-Za-z0-9_]/g, '_')}` }
function sanitizeComment(s: string): string {
  return s.replace(/[\r\n]+/g, ' ').replace(/\b(import|require|Function|eval)\b/g, w => `${w.slice(0, 1)}_${w.slice(1)}`)
}

// --- Kind TypeScript types, defaults & validation --------------------------------------------------------------------

function kindTsType(k: KindInfo): string {
  switch (k.kind) {
    case 'nat': case 'int': case 'decimal': return 'number'
    case 'bool': return 'boolean'
    case 'oneOf': return k.values.map(v => JSON.stringify(v)).join(' | ')
    case 'maybe': return `${kindTsType(k.of)} | null`
    case 'record': return `{ ${k.fields.map(([f, fk]) => `readonly ${propKey(f)}: ${kindTsType(fk)}`).join('; ')} }`
    case 'variant': return k.cases.map(([c, fs]) => {
      const rest = fs.map(([f, fk]) => `readonly ${propKey(f)}: ${kindTsType(fk)}`).join('; ')
      return `{ readonly ${propKey(k.tagKey)}: ${JSON.stringify(c)}${rest ? `; ${rest}` : ''} }`
    }).join(' | ')
    case 'str': return 'string'
    case 'fixed': return k.width === 64 ? 'string' : 'number'
    case 'unknown': return 'number'
  }
}

function kindDefaultTs(k: KindInfo): string {
  switch (k.kind) {
    case 'nat': case 'int': case 'decimal': return '0'
    case 'bool': return 'false'
    case 'oneOf': return JSON.stringify(k.values[0]!)
    case 'maybe': return 'null'
    case 'record': return `{ ${k.fields.map(([f, fk]) => `${propKey(f)}: ${kindDefaultTs(fk)}`).join(', ')} }`
    case 'variant': {
      const [c, fs] = k.cases[0]!
      const rest = fs.map(([f, fk]) => `${propKey(f)}: ${kindDefaultTs(fk)}`).join(', ')
      return `{ ${propKey(k.tagKey)}: ${JSON.stringify(c)}${rest ? `, ${rest}` : ''} }`
    }
    case 'str': return "''"
    case 'fixed': return k.width === 64 ? "'0'" : '0'
    case 'unknown': return '0'
  }
}

function decimalPlacesIn(k: KindInfo, out: Set<number> = new Set()): Set<number> {
  if (k.kind === 'decimal') out.add(k.places)
  else if (k.kind === 'maybe') decimalPlacesIn(k.of, out)
  else if (k.kind === 'record') for (const [, fk] of k.fields) decimalPlacesIn(fk, out)
  else if (k.kind === 'variant') for (const [, fs] of k.cases) for (const [, fk] of fs) decimalPlacesIn(fk, out)
  return out
}

function decimalRoundedPlacesIn(k: KindInfo, out: Set<number> = new Set()): Set<number> {
  if (k.kind === 'decimal' && k.round === 'half-even') out.add(k.places)
  else if (k.kind === 'maybe') decimalRoundedPlacesIn(k.of, out)
  else if (k.kind === 'record') for (const [, fk] of k.fields) decimalRoundedPlacesIn(fk, out)
  else if (k.kind === 'variant') for (const [, fs] of k.cases) for (const [, fk] of fs) decimalRoundedPlacesIn(fk, out)
  return out
}

function kindGuardChecks(k: KindInfo, expr: string): string[] {
  switch (k.kind) {
    case 'nat': {
      const checks = [`(!Number.isSafeInteger(${expr}) || ${expr} < 0)`]
      if (k.max !== undefined) checks.push(`(${expr} > ${k.max})`)
      return checks
    }
    case 'int':
      return [`!Number.isSafeInteger(${expr})`]
    case 'oneOf':
      return [`!(${k.values.map(v => `${expr} === ${JSON.stringify(v)}`).join(' || ')})`]
    case 'maybe': {
      const inner = kindGuardChecks(k.of, expr)
      return inner.length ? [`(${expr} !== null && (${inner.join(' || ')}))`] : []
    }
    case 'record':
      return k.fields.flatMap(([f, fk]) => kindGuardChecks(fk, propAccess(expr, f)))
    case 'variant':
      return k.cases.flatMap(([c, fs]) => {
        const inner = fs.flatMap(([f, fk]) => kindGuardChecks(fk, propAccess(expr, f)))
        return inner.length ? [`(${propAccess(expr, k.tagKey)} === ${JSON.stringify(c)} && (${inner.join(' || ')}))`] : []
      })
    case 'str':
      return k.maxLength !== undefined ? [`(${expr}.length > ${k.maxLength})`] : []
    case 'bool':
    case 'decimal':
    case 'fixed':
    case 'unknown':
      return []
  }
}

// --- AST equality & linear-form cancellation -------------------------------------------------------------------------

const sameNode = (a: unknown, b: unknown): boolean => a === b || JSON.stringify(a) === JSON.stringify(b)

type LinForm = {
  vars: Map<string, number>
  signed: Map<string, number>
  constVal: number
  rest: {coeff: number, e: E}[]
}

function emptyLin(): LinForm { return {vars: new Map(), signed: new Map(), constVal: 0, rest: []} }

function addLin(dst: LinForm, e: E, scale: number): void {
  if (scale === 0) return
  switch (e.op) {
    case 'const': dst.constVal += scale * e.value; return
    case 'var': dst.vars.set(e.name, (dst.vars.get(e.name) ?? 0) + scale); return
    case 'add': addLin(dst, e.a, scale); addLin(dst, e.b, scale); return
    case 'mul': addLin(dst, e.a, scale * e.k); return
    case 'sub':
    case 'prod':
    case 'min':
    case 'max':
    case 'if':
    case 'get':
    case 'tup':
    case 'proj':
      dst.rest.push({coeff: scale, e})
      return
  }
}

function cancelSigned(lin: LinForm, signedVars: ReadonlySet<string>): void {
  for (const name of signedVars) {
    const neg = `${name}$neg`
    const p = lin.vars.get(name) ?? 0
    const qv = lin.vars.get(neg) ?? 0
    if (p === 0 || qv === 0) continue
    if (p > 0 && qv < 0) {
      const k = Math.min(p, -qv)
      lin.vars.set(name, p - k)
      lin.vars.set(neg, qv + k)
      lin.signed.set(name, (lin.signed.get(name) ?? 0) + k)
    } else if (p < 0 && qv > 0) {
      const k = Math.min(-p, qv)
      lin.vars.set(name, p + k)
      lin.vars.set(neg, qv - k)
      lin.signed.set(name, (lin.signed.get(name) ?? 0) - k)
    }
  }
  for (const [k, v] of [...lin.vars]) if (v === 0) lin.vars.delete(k)
  for (const [k, v] of [...lin.signed]) if (v === 0) lin.signed.delete(k)
}

// --- Slot registration for Kind trees --------------------------------------------------------------------------------

type Slot =
  | {kind: 'nat', ts: string}
  | {kind: 'bool', ts: string}
  | {kind: 'oneOf', ts: string, values: readonly string[]}
  | {kind: 'intPos', ts: string, base: string}
  | {kind: 'intNeg', ts: string, base: string}
  | {kind: 'maybeSome', ts: string}
  | {kind: 'variantTag', ts: string, tagKey: string, cases: readonly string[]}
  | {kind: 'strId', ts: string, patterns: readonly string[]}
  | {kind: 'strLen', ts: string}
  | {kind: 'strLike', ts: string, pattern: string}

type SlotRegistry = {
  slots: Map<string, Slot>
  signedVars: Set<string>
  signedTs: Map<string, string>
  strLiterals: Map<number, string>
}

function makeRegistry(): SlotRegistry {
  const strLiterals = new Map<number, string>()
  for (const [text, id] of interned()) strLiterals.set(id, text)
  return {slots: new Map(), signedVars: new Set(), signedTs: new Map(), strLiterals}
}

function registerKind(reg: SlotRegistry, rawName: string, kind: KindInfo, tsExpr: string, guard?: string): void {
  const wrap = (expr: string, fallback: string) => (guard ? `(${guard} ? ${expr} : ${fallback})` : expr)
  switch (kind.kind) {
    case 'nat':
    case 'unknown':
      reg.slots.set(rawName, {kind: 'nat', ts: wrap(tsExpr, '0')})
      return
    case 'bool':
      reg.slots.set(rawName, {kind: 'bool', ts: wrap(tsExpr, 'false')})
      return
    case 'oneOf':
      reg.slots.set(rawName, {kind: 'oneOf', ts: wrap(tsExpr, JSON.stringify(kind.values[0]!)), values: kind.values})
      return
    case 'int':
    case 'decimal':
      reg.signedVars.add(rawName)
      reg.signedTs.set(rawName, wrap(tsExpr, '0'))
      reg.slots.set(rawName, {kind: 'intPos', ts: wrap(tsExpr, '0'), base: rawName})
      reg.slots.set(`${rawName}$neg`, {kind: 'intNeg', ts: wrap(tsExpr, '0'), base: rawName})
      return
    case 'maybe': {
      reg.slots.set(`${rawName}$some`, {kind: 'maybeSome', ts: wrap(tsExpr, 'null')})
      const innerGuard = guard ? `${guard} && ${tsExpr} !== null` : `${tsExpr} !== null`
      registerKind(reg, rawName, kind.of, tsExpr, innerGuard)
      return
    }
    case 'record':
      for (const [f, fk] of kind.fields) registerKind(reg, `${rawName}.${f}`, fk, propAccess(tsExpr, f), guard)
      return
    case 'variant': {
      const names = kind.cases.map(([c]) => c)
      reg.slots.set(rawName, {kind: 'variantTag', ts: wrap(tsExpr, kindDefaultTs(kind)), tagKey: kind.tagKey, cases: names})
      for (const [c, fs] of kind.cases) {
        const caseGuard = guard ? `${guard} && ${propAccess(tsExpr, kind.tagKey)} === ${JSON.stringify(c)}` : `${propAccess(tsExpr, kind.tagKey)} === ${JSON.stringify(c)}`
        for (const [f, fk] of fs) registerKind(reg, `${rawName}.${c}.${f}`, fk, propAccess(tsExpr, f), caseGuard)
      }
      return
    }
    case 'str':
      reg.slots.set(rawName, {kind: 'strId', ts: wrap(tsExpr, "''"), patterns: kind.patterns})
      reg.slots.set(`${rawName}$len`, {kind: 'strLen', ts: wrap(`${tsExpr}.length`, '0')})
      kind.patterns.forEach((p, i) => {
        reg.slots.set(`${rawName}$like${i}`, {kind: 'strLike', ts: wrap(tsExpr, "''"), pattern: p})
      })
      return
    case 'fixed': {
      const limbs = kind.width === 8 ? 1 : kind.width / 16
      for (let i = 0; i < limbs; i++) reg.slots.set(`${rawName}$${i}`, {kind: 'nat', ts: `${safeVar('$limb_', rawName)}_${i}`})
      return
    }
  }
}

// --- Expression & condition emitter ----------------------------------------------------------------------------------

type MapInfo = {
  readonly rawName: string
  readonly mapName: string
  readonly stateExpr: string
  readonly defaultVal: number
  readonly fieldKind?: KindInfo
  readonly dynamicDefaultExpr?: string
  readonly getterTpl?: string
}

type EmitCtx = {
  readonly reg: SlotRegistry
  readonly flags: Map<string, string>
  readonly maps: Map<string, MapInfo>
  readonly fns: Record<string, Fn>
  readonly helpers: Set<'glob' | 'cpair' | 'cunpair' | 'dec' | 'decRound' | 'idx'>
  readonly fnNames: Map<string, string>
  readonly boundKeys: Map<string, string>
  readonly cse: Map<string, {ts: string, kind: KindInfo}>
}

function emitTsCode(ctx: EmitCtx) {
  const slotAsNum = (name: string): string => {
    if (ctx.boundKeys.has(name)) return ctx.boundKeys.get(name)!
    const s = ctx.reg.slots.get(name)
    if (!s) return name
    switch (s.kind) {
      case 'nat': case 'strLen': return s.ts
      case 'bool': return `(${s.ts} ? 1 : 0)`
      case 'maybeSome': return `(${s.ts} !== null ? 1 : 0)`
      case 'intPos': return `Math.max(${s.ts}, 0)`
      case 'intNeg': return `Math.max(-(${s.ts}), 0)`
      case 'oneOf': {
        ctx.helpers.add('idx')
        return `$idx(${s.ts}, [${s.values.map(v => JSON.stringify(v)).join(', ')}])`
      }
      case 'variantTag': {
        ctx.helpers.add('idx')
        return `$idx(${propAccess(s.ts, s.tagKey)}, [${s.cases.map(v => JSON.stringify(v)).join(', ')}])`
      }
      case 'strLike': {
        ctx.helpers.add('glob')
        return `($globMatch(${JSON.stringify(s.pattern)}, ${s.ts}) ? 1 : 0)`
      }
      case 'strId':
        return s.ts
    }
  }

  const mapReadExpr = (rawMap: string, keyE: E): {expr: string, kind: KindInfo} => {
    const info = ctx.maps.get(rawMap)
    if (!info) throw new Error(`emit: unknown map ${rawMap}`)
    const kTs = emitNum(keyE)
    if (info.getterTpl) return {expr: info.getterTpl.replace('__K__', kTs), kind: info.fieldKind ?? {kind: 'nat'}}
    const def = info.dynamicDefaultExpr ?? String(info.defaultVal)
    return {expr: `(${info.stateExpr}.get(${kTs}) ?? ${def})`, kind: info.fieldKind ?? {kind: 'nat'}}
  }

  const emitFnCall = (map: string, key: E): string | undefined => {
    const mDiv = /^(div|mod)\$(\d+)$/.exec(map)
    if (mDiv) {
      const k = Number(mDiv[2]), a = emitNum(key)
      return mDiv[1] === 'div' ? `Math.floor(${a} / ${k})` : `(${a} % ${k})`
    }
    const fn = ctx.fns[map]
    if (!fn) return undefined
    const direct = directOf(fn)
    if (direct?.kind === 'div') return `Math.floor(${emitNum(key)} / ${direct.divisor})`
    if (direct?.kind === 'mod') return `(${emitNum(key)} % ${direct.divisor})`
    if (direct?.kind === 'const') return String(direct.value)
    const arity = fn.arity ?? 1
    const fnId = ctx.fnNames.get(map)!
    if (arity > 1) {
      const args = pairedArgs(key, arity)
      if (args) return `${fnId}(${args.map(emitNum).join(', ')})`
    }
    return `${fnId}(${emitNum(key)})`
  }

  const emitNum = (e: E): string => {
    if (ctx.cse.size) {
      const hit = ctx.cse.get(JSON.stringify(e))
      if (hit?.kind.kind === 'nat') return hit.ts
    }
    switch (e.op) {
      case 'const': return String(e.value)
      case 'var': return slotAsNum(e.name)
      case 'add': {
        const lin = emptyLin()
        addLin(lin, e, 1)
        cancelSigned(lin, ctx.reg.signedVars)
        return formatLin(lin)
      }
      case 'sub': return `Math.max(0, ${emitNum(e.a)} - ${emitNum(e.b)})`
      case 'mul': return e.k === 0 ? '0' : e.k === 1 ? emitNum(e.a) : `(${e.k} * ${emitNum(e.a)})`
      case 'prod': return `(${emitNum(e.a)} * ${emitNum(e.b)})`
      case 'min': return `Math.min(${emitNum(e.a)}, ${emitNum(e.b)})`
      case 'max': return `Math.max(${emitNum(e.a)}, ${emitNum(e.b)})`
      case 'if': return `(${emitCond(e.c)} ? ${emitNum(e.then)} : ${emitNum(e.else)})`
      case 'tup': ctx.helpers.add('cpair'); return `$cpair(${emitNum(e.a)}, ${emitNum(e.b)})`
      case 'proj': ctx.helpers.add('cunpair'); return `$cunpair(${emitNum(e.a)})[${e.k}]`
      case 'get': {
        const fnExpr = emitFnCall(e.map, e.key)
        if (fnExpr !== undefined) return fnExpr
        const r = mapReadExpr(e.map, e.key)
        if (r.kind.kind === 'bool') return `(${r.expr} ? 1 : 0)`
        if (r.kind.kind === 'oneOf') {
          ctx.helpers.add('idx')
          return `$idx(${r.expr}, [${r.kind.values.map(v => JSON.stringify(v)).join(', ')}])`
        }
        return r.expr
      }
    }
  }

  const formatLin = (lin: LinForm): string => {
    const pos: string[] = [], neg: string[] = []
    const push = (expr: string, c: number) => {
      if (c === 1) pos.push(expr)
      else if (c === -1) neg.push(expr)
      else if (c > 1) pos.push(`${c} * ${expr}`)
      else if (c < -1) neg.push(`${-c} * ${expr}`)
    }
    for (const [k, c] of lin.signed) push(ctx.reg.signedTs.get(k)!, c)
    for (const [k, c] of lin.vars) push(slotAsNum(k), c)
    for (const r of lin.rest) push(emitNum(r.e), r.coeff)
    if (lin.constVal > 0) pos.push(String(lin.constVal))
    else if (lin.constVal < 0) neg.push(String(-lin.constVal))
    if (!pos.length && !neg.length) return '0'
    if (!neg.length) return pos.length === 1 ? pos[0]! : `(${pos.join(' + ')})`
    if (!pos.length) return neg.length === 1 ? `(-${neg[0]!})` : `(-(${neg.join(' + ')}))`
    return `(${pos.join(' + ')} - ${neg.join(' - ')})`
  }

  const emitSignedDiff = (a: E, b: E): string => {
    if (a.op === 'sub' && b.op === 'sub' && sameNode(a.a, b.b) && sameNode(a.b, b.a)) return emitSignedDiff(a.a, a.b)
    if (a.op === 'if' && b.op === 'if' && sameNode(a.c, b.c)) return `(${emitCond(a.c)} ? ${emitSignedDiff(a.then, b.then)} : ${emitSignedDiff(a.else, b.else)})`
    const lin = emptyLin()
    addLin(lin, a, 1)
    addLin(lin, b, -1)
    cancelSigned(lin, ctx.reg.signedVars)
    return formatLin(lin)
  }

  const choiceSlotOf = (e: E): {ts: string, values: readonly string[]} | undefined => {
    if (ctx.cse.size) {
      const hit = ctx.cse.get(JSON.stringify(e))
      if (hit?.kind.kind === 'oneOf') return {ts: hit.ts, values: hit.kind.values}
    }
    if (e.op === 'var') {
      const s = ctx.reg.slots.get(e.name)
      if (s?.kind === 'oneOf') return {ts: s.ts, values: s.values}
      if (s?.kind === 'variantTag') return {ts: propAccess(s.ts, s.tagKey), values: s.cases}
    }
    if (e.op === 'get' && ctx.maps.has(e.map)) {
      const info = ctx.maps.get(e.map)!
      if (info.fieldKind?.kind === 'oneOf') return {ts: mapReadExpr(e.map, e.key).expr, values: info.fieldKind.values}
      if (info.fieldKind?.kind === 'variant') return {ts: propAccess(mapReadExpr(e.map, e.key).expr, info.fieldKind.tagKey), values: info.fieldKind.cases.map(([c]) => c)}
    }
    return undefined
  }

  const boolSlotOf = (e: E): string | undefined => {
    if (ctx.cse.size) {
      const hit = ctx.cse.get(JSON.stringify(e))
      if (hit?.kind.kind === 'bool') return hit.ts
    }
    if (e.op === 'var') {
      const s = ctx.reg.slots.get(e.name)
      if (s?.kind === 'bool') return s.ts
      if (s?.kind === 'maybeSome') return `(${s.ts} !== null)`
      if (s?.kind === 'strLike') { ctx.helpers.add('glob'); return `$globMatch(${JSON.stringify(s.pattern)}, ${s.ts})` }
    }
    if (e.op === 'get' && ctx.maps.has(e.map)) {
      const info = ctx.maps.get(e.map)!
      if (info.fieldKind?.kind === 'bool') return mapReadExpr(e.map, e.key).expr
    }
    return undefined
  }

  const emitCmp = (op: '<' | '<=' | '=', a: E, b: E, negated = false): string => {
    if (a.op === 'const' && b.op === 'const') {
      const res = op === '<' ? a.value < b.value : op === '<=' ? a.value <= b.value : a.value === b.value
      return String(negated ? !res : res)
    }
    if (op === '=') {
      const ba = boolSlotOf(a), bb = boolSlotOf(b)
      if (ba && b.op === 'const' && (b.value === 0 || b.value === 1)) return (b.value === 1) !== negated ? ba : `!(${ba})`
      if (bb && a.op === 'const' && (a.value === 0 || a.value === 1)) return (a.value === 1) !== negated ? bb : `!(${bb})`
      if (ba && bb) return negated ? `(${ba} !== ${bb})` : `(${ba} === ${bb})`
      const ca = choiceSlotOf(a), cb = choiceSlotOf(b)
      if (ca && b.op === 'const' && b.value >= 0 && b.value < ca.values.length) return `(${ca.ts} ${negated ? '!==' : '==='} ${JSON.stringify(ca.values[b.value]!)})`
      if (cb && a.op === 'const' && a.value >= 0 && a.value < cb.values.length) return `(${cb.ts} ${negated ? '!==' : '==='} ${JSON.stringify(cb.values[a.value]!)})`
      if (ca && cb && ca.values.join('\0') === cb.values.join('\0')) return `(${ca.ts} ${negated ? '!==' : '==='} ${cb.ts})`
      if (a.op === 'var' && ctx.reg.slots.get(a.name)?.kind === 'strId') {
        const sA = ctx.reg.slots.get(a.name)!
        if (b.op === 'const' && ctx.reg.strLiterals.has(b.value)) return `(${sA.ts} ${negated ? '!==' : '==='} ${JSON.stringify(ctx.reg.strLiterals.get(b.value)!)})`
        if (b.op === 'var' && ctx.reg.slots.get(b.name)?.kind === 'strId') return `(${sA.ts} ${negated ? '!==' : '==='} ${ctx.reg.slots.get(b.name)!.ts})`
      }
    }
    // Simplify 0/1 boolean range comparisons (e.g. bool <= 1 -> true)
    const baR = boolSlotOf(a), bbR = boolSlotOf(b)
    if (baR && b.op === 'const') {
      const vals = [0, 1].filter(i => { const ok = op === '<' ? i < b.value : op === '<=' ? i <= b.value : i === b.value; return negated ? !ok : ok })
      if (vals.length === 0) return 'false'
      if (vals.length === 2) return 'true'
      return vals[0] === 1 ? baR : `!(${baR})`
    }
    if (bbR && a.op === 'const') {
      const vals = [0, 1].filter(i => { const ok = op === '<' ? a.value < i : op === '<=' ? a.value <= i : a.value === i; return negated ? !ok : ok })
      if (vals.length === 0) return 'false'
      if (vals.length === 2) return 'true'
      return vals[0] === 1 ? bbR : `!(${bbR})`
    }
    // Simplify oneOf index range comparisons (e.g. Chart's `among` range tests)
    const ca = choiceSlotOf(a), cb = choiceSlotOf(b)
    if (ca && b.op === 'const') {
      const keep = ca.values.filter((_, i) => { const ok = op === '<' ? i < b.value : op === '<=' ? i <= b.value : i === b.value; return negated ? !ok : ok })
      if (keep.length === 0) return 'false'
      if (keep.length === ca.values.length) return 'true'
      return `(${keep.map(v => `${ca.ts} === ${JSON.stringify(v)}`).join(' || ')})`
    }
    if (cb && a.op === 'const') {
      const keep = cb.values.filter((_, i) => { const ok = op === '<' ? a.value < i : op === '<=' ? a.value <= i : a.value === i; return negated ? !ok : ok })
      if (keep.length === 0) return 'false'
      if (keep.length === cb.values.length) return 'true'
      return `(${keep.map(v => `${cb.ts} === ${JSON.stringify(v)}`).join(' || ')})`
    }
    // Linear cancellation for signed Int/Decimal comparisons
    const lin = emptyLin()
    addLin(lin, a, 1)
    addLin(lin, b, -1)
    cancelSigned(lin, ctx.reg.signedVars)
    const lhs = emptyLin(), rhs = emptyLin()
    for (const [k, c] of lin.signed) { if (c > 0) lhs.signed.set(k, c); else rhs.signed.set(k, -c) }
    for (const [k, c] of lin.vars) { if (c > 0) lhs.vars.set(k, c); else rhs.vars.set(k, -c) }
    for (const r of lin.rest) { if (r.coeff > 0) lhs.rest.push(r); else rhs.rest.push({coeff: -r.coeff, e: r.e}) }
    const lhsHas = lhs.signed.size + lhs.vars.size + lhs.rest.length > 0
    const rhsHas = rhs.signed.size + rhs.vars.size + rhs.rest.length > 0
    if (lhsHas && !rhsHas) rhs.constVal = -lin.constVal
    else if (!lhsHas && rhsHas) lhs.constVal = lin.constVal
    else if (lin.constVal >= 0) lhs.constVal = lin.constVal
    else rhs.constVal = -lin.constVal
    const effOp = !negated ? (op === '=' ? '===' : op) : (op === '<' ? '>=' : op === '<=' ? '>' : '!==')
    return `(${formatLin(lhs)} ${effOp} ${formatLin(rhs)})`
  }

  const emitCond = (c: C): string => {
    switch (c.op) {
      case '<': case '<=': case '=': return emitCmp(c.op, c.a, c.b, false)
      case 'not': {
        if (c.x.op === 'not') return emitCond(c.x.x)
        if (c.x.op === '<' || c.x.op === '<=' || c.x.op === '=') return emitCmp(c.x.op, c.x.a, c.x.b, true)
        const inner = emitCond(c.x)
        return inner === 'true' ? 'false' : inner === 'false' ? 'true' : `!(${inner})`
      }
      case 'and': {
        const parts: string[] = []
        for (const x of c.xs) {
          const s = emitCond(x)
          if (s === 'false') return 'false'
          if (s !== 'true' && !parts.includes(s)) parts.push(s)
        }
        return parts.length === 0 ? 'true' : parts.length === 1 ? parts[0]! : `(${parts.join(' && ')})`
      }
      case 'or': {
        const parts: string[] = []
        for (const x of c.xs) {
          const s = emitCond(x)
          if (s === 'true') return 'true'
          if (s !== 'false' && !parts.includes(s)) parts.push(s)
        }
        return parts.length === 0 ? 'false' : parts.length === 1 ? parts[0]! : `(${parts.join(' || ')})`
      }
      case 'flag': return ctx.flags.get(c.name) ?? c.name
      case 'all': throw new Error('emit: quantified condition in runtime code is not supported yet')
    }
  }

  const emitBoolVal = (e: E): string => {
    if (e.op === 'const') return e.value === 0 ? 'false' : 'true'
    const b = boolSlotOf(e)
    if (b) return b
    if (e.op === 'if') {
      if (e.then.op === 'const' && e.then.value === 1 && e.else.op === 'const' && e.else.value === 0) return emitCond(e.c)
      if (e.then.op === 'const' && e.then.value === 0 && e.else.op === 'const' && e.else.value === 1) return emitCond({op: 'not', x: e.c})
      return `(${emitCond(e.c)} ? ${emitBoolVal(e.then)} : ${emitBoolVal(e.else)})`
    }
    return `(${emitNum(e)} !== 0)`
  }

  const emitChoiceVal = (e: E, values: readonly string[]): string => {
    if (e.op === 'const' && e.value >= 0 && e.value < values.length) return JSON.stringify(values[e.value]!)
    const ch = choiceSlotOf(e)
    if (ch && ch.values.join('\0') === values.join('\0')) return ch.ts
    if (e.op === 'if') return `(${emitCond(e.c)} ? ${emitChoiceVal(e.then, values)} : ${emitChoiceVal(e.else, values)})`
    return `([${values.map(v => JSON.stringify(v)).join(', ')}] as const)[${emitNum(e)}] ?? ${JSON.stringify(values[0]!)}`
  }

  const emitStrVal = (e: E): string => {
    if (e.op === 'const' && ctx.reg.strLiterals.has(e.value)) return JSON.stringify(ctx.reg.strLiterals.get(e.value)!)
    if (e.op === 'var' && ctx.reg.slots.get(e.name)?.kind === 'strId') return ctx.reg.slots.get(e.name)!.ts
    if (e.op === 'if') return `(${emitCond(e.c)} ? ${emitStrVal(e.then)} : ${emitStrVal(e.else)})`
    return "''"
  }

  const emitVariantVal = (kind: Extract<KindInfo, {kind: 'variant'}>, baseName: string, getE: (part: string) => E): string => {
    const tagE = getE(baseName)
    const walkTag = (t: E, branch: (e: E) => E): string => {
      if (t.op === 'if') {
        const cond = emitCond(t.c)
        return `(${cond} ? ${walkTag(t.then, e => (e.op === 'if' && sameNode(e.c, t.c) ? branch(e.then) : branch(e)))} : ${walkTag(t.else, e => (e.op === 'if' && sameNode(e.c, t.c) ? branch(e.else) : branch(e)))})`
      }
      if (t.op === 'var') {
        const s = ctx.reg.slots.get(t.name)
        if (s?.kind === 'variantTag' && s.cases.join('\0') === kind.cases.map(([c]) => c).join('\0')) return s.ts
      }
      if (t.op === 'get' && ctx.maps.has(t.map)) {
        const info = ctx.maps.get(t.map)!
        if (info.fieldKind?.kind === 'variant' && info.fieldKind.cases.map(([c]) => c).join('\0') === kind.cases.map(([c]) => c).join('\0')) {
          return mapReadExpr(t.map, t.key).expr
        }
      }
      if (t.op === 'const' && t.value >= 0 && t.value < kind.cases.length) {
        const [caseName, fields] = kind.cases[t.value]!
        const fStr = fields.map(([f, fk]) => `${propKey(f)}: ${emitKindVal(fk, `${baseName}.${caseName}.${f}`, part => branch(getE(part)))}`).join(', ')
        return `{ ${propKey(kind.tagKey)}: ${JSON.stringify(caseName)}${fStr ? `, ${fStr}` : ''} }`
      }
      const idx = emitNum(t)
      return kind.cases.slice(0, -1).reduceRight((acc, [caseName, fields], i) => {
        const fStr = fields.map(([f, fk]) => `${propKey(f)}: ${emitKindVal(fk, `${baseName}.${caseName}.${f}`, part => branch(getE(part)))}`).join(', ')
        return `(${idx} === ${i} ? { ${propKey(kind.tagKey)}: ${JSON.stringify(caseName)}${fStr ? `, ${fStr}` : ''} } : ${acc})`
      }, (() => {
        const [caseName, fields] = kind.cases.at(-1)!
        const fStr = fields.map(([f, fk]) => `${propKey(f)}: ${emitKindVal(fk, `${baseName}.${caseName}.${f}`, part => branch(getE(part)))}`).join(', ')
        return `{ ${propKey(kind.tagKey)}: ${JSON.stringify(caseName)}${fStr ? `, ${fStr}` : ''} }`
      })())
    }
    return walkTag(tagE, e => e)
  }

  const emitKindVal = (kind: KindInfo, baseName: string, getE: (part: string) => E): string => {
    switch (kind.kind) {
      case 'nat': case 'unknown': return emitNum(getE(baseName))
      case 'bool': return emitBoolVal(getE(baseName))
      case 'oneOf': return emitChoiceVal(getE(baseName), kind.values)
      case 'int': case 'decimal': return emitSignedDiff(getE(baseName), getE(`${baseName}$neg`))
      case 'maybe': {
        const some = emitBoolVal(getE(`${baseName}$some`))
        if (some === 'false') return 'null'
        if (some === 'true') return emitKindVal(kind.of, baseName, getE)
        return `(${some} ? ${emitKindVal(kind.of, baseName, getE)} : null)`
      }
      case 'record':
        return `{ ${kind.fields.map(([f, fk]) => `${propKey(f)}: ${emitKindVal(fk, `${baseName}.${f}`, getE)}`).join(', ')} }`
      case 'variant':
        return emitVariantVal(kind, baseName, getE)
      case 'str':
        return emitStrVal(getE(baseName))
      case 'fixed': {
        const limbs = kind.width === 8 ? 1 : kind.width / 16
        const base = kind.width === 8 ? 256n : 65536n
        let acc = '0n'
        for (let i = limbs - 1; i >= 0; i--) acc = `(${acc} * ${base}n + BigInt(${emitNum(getE(`${baseName}$${i}`))}))`
        if (kind.signed) {
          const half = 1n << BigInt(kind.width - 1)
          const full = 1n << BigInt(kind.width)
          acc = `((v => v >= ${half}n ? v - ${full}n : v)(${acc}))`
        }
        return kind.width === 64 ? `String(${acc})` : `Number(${acc})`
      }
    }
  }

  return {emitNum, emitCond, emitSignedDiff, emitBoolVal, emitChoiceVal, emitKindVal}
}

// --- Helper functions emitted only when used -------------------------------------------------------------------------

function renderHelpers(helpers: ReadonlySet<string>): string[] {
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
      '  const v = s % 2 === 0 ? (s / 2) * (s + 1) + b : s * ((s + 1) / 2) + b',
      "  if (!Number.isSafeInteger(v)) throw new RangeError('tuple key passed safe integer range')",
      '  return v',
      '}',
    )
  }
  if (helpers.has('cunpair')) {
    out.push(
      'function $cunpair(z: number): readonly [number, number] {',
      '  const tri = (s: number) => (s % 2 === 0 ? (s / 2) * (s + 1) : s * ((s + 1) / 2))',
      '  let s = Math.floor((Math.sqrt(8 * z + 1) - 1) / 2)',
      '  while (s > 0 && tri(s) > z) s--',
      '  while (tri(s + 1) <= z) s++',
      '  const b = z - tri(s)',
      '  return [s - b, b]',
      '}',
    )
  }
  return out
}

// --- Direct recurrence / custom fn emitter ---------------------------------------------------------------------------

function emitRuleFnHelper(fnId: string, fn: Fn): string[] {
  const direct = directOf(fn)
  if (direct?.kind === 'recur') return emitRecurHelper(fnId, direct)
  const arity = fn.arity ?? 1
  const params = Array.from({length: arity}, (_, i) => `a${i}: number`).join(', ')
  return [`const ${fnId} = (${fn.call ?? fn.js}) as (${params}) => number`]
}

function emitRecurHelper(fnId: string, d: Extract<DirectFn, {kind: 'recur'}>): string[] {
  const lines: string[] = []
  const useNames = new Map<string, string>()
  let ui = 0
  for (const [u, ufn] of Object.entries(d.uses)) {
    const uid = `${fnId}_u${ui++}`
    useNames.set(u, uid)
    const ud = directOf(ufn)
    if (ud?.kind === 'div') lines.push(`function ${uid}(x: number): number { return Math.floor(x / ${ud.divisor}) }`)
    else if (ud?.kind === 'mod') lines.push(`function ${uid}(x: number): number { return x % ${ud.divisor} }`)
    else if (ud?.kind === 'const') lines.push(`function ${uid}(): number { return ${ud.value} }`)
    else if (ud?.kind === 'recur') lines.push(...emitRecurHelper(uid, ud))
    else lines.push(...emitRuleFnHelper(uid, ufn))
  }
  const emitE = (e: E): string => {
    switch (e.op) {
      case 'var': return e.name
      case 'const': return String(e.value)
      case 'add': return `(${emitE(e.a)} + ${emitE(e.b)})`
      case 'sub': return `Math.max(0, ${emitE(e.a)} - ${emitE(e.b)})`
      case 'mul': return `(${e.k} * ${emitE(e.a)})`
      case 'prod': return `(${emitE(e.a)} * ${emitE(e.b)})`
      case 'min': return `Math.min(${emitE(e.a)}, ${emitE(e.b)})`
      case 'max': return `Math.max(${emitE(e.a)}, ${emitE(e.b)})`
      case 'if': return `(${emitC(e.c)} ? ${emitE(e.then)} : ${emitE(e.else)})`
      case 'get': {
        const ufn = d.uses[e.map]!, uid = useNames.get(e.map)!, arity = ufn.arity ?? 1
        const args = arity > 1 ? pairedArgs(e.key, arity) : undefined
        return args ? `${uid}(${args.map(emitE).join(', ')})` : `${uid}(${emitE(e.key)})`
      }
      case 'tup': case 'proj': throw new Error('emit: tuple in recurrence')
    }
  }
  const emitC = (c: C): string => {
    switch (c.op) {
      case '<': return `(${emitE(c.a)} < ${emitE(c.b)})`
      case '<=': return `(${emitE(c.a)} <= ${emitE(c.b)})`
      case '=': return `(${emitE(c.a)} === ${emitE(c.b)})`
      case 'and': return c.xs.length ? `(${c.xs.map(emitC).join(' && ')})` : 'true'
      case 'or': return c.xs.length ? `(${c.xs.map(emitC).join(' || ')})` : 'false'
      case 'not': return `!(${emitC(c.x)})`
      case 'flag': case 'all': throw new Error('emit: flag/quantifier in recurrence')
    }
  }
  const sig = ['n: number', ...d.args.map(a => `${a}: number`)].join(', ')
  lines.push(
    `function ${fnId}(${sig}): number {`,
    `  let prev = ${emitE(d.zero)}`,
    '  for (let x = 0; x < n; x++) {',
    `    prev = ${emitE(d.next)}`,
    `    if (!Number.isSafeInteger(prev)) throw new RangeError(${JSON.stringify(`${d.name}: exceeded safe integer range`)})`,
    '  }',
    '  return prev',
    '}',
  )
  return lines
}

// --- Header comment formatter ----------------------------------------------------------------------------------------

function renderHeader(info: {
  name: string
  kind: 'rule' | 'fun' | 'ratRule' | 'chart'
  digest: string
  arithmetic: string
  laws: readonly EmitLawReport[]
  provenance?: EmitProvenance
}): string[] {
  const label = info.kind === 'fun' ? 'Pure rule' : info.kind === 'ratRule' ? 'Rational rule' : info.kind === 'chart' ? 'Statechart' : 'Rule'
  const lead = info.provenance
    ? [
        `// Generated by gdp-wired ${GDP_WIRED_VERSION} from ${sanitizeComment(info.provenance.model)}. Do not edit.`,
        `// To change behavior, edit the model and its laws, then run from the repository root: npx gdp-wired-cli emit ${sanitizeComment(info.provenance.model)}${info.provenance.out ? ` --out ${sanitizeComment(info.provenance.out)}` : ''}`,
      ]
    : [`// Generated by gdp-wired ${GDP_WIRED_VERSION}. Do not edit.`]
  const lines = [
    ...lead,
    `// ${label}: ${sanitizeComment(info.name)}`,
    `// Digest: ${info.digest}`,
    `// Arithmetic: ${info.arithmetic}`,
    '// Proven laws:',
  ]
  if (info.laws.length === 0) {
    lines.push('//   (none)')
  } else {
    for (const l of info.laws) {
      const status = l.proven && l.checked
        ? (l.assumes?.length ? `proven with assumptions (${l.assumes.join('; ')})` : 'proven, kernel-checked')
        : `UNPROVEN (${sanitizeComment(l.why ?? l.goal ?? 'not proven')})`
      lines.push(`//   - [${l.kind}] ${sanitizeComment(l.name)}: ${status}`)
    }
  }
  return lines
}

// --- emitFun ---------------------------------------------------------------------------------------------------------

export function emitFun(f: AnyFun, opts: EmitFunOptions = {}): EmitResult {
  const meta = inspectFunMeta(f)
  const laws = opts.laws ? [...opts.laws] : meta.ownedLaws
  const reports: EmitLawReport[] = []
  let allProven = laws.length > 0
  let firstFailed: Verdict | undefined
  for (const d of laws) {
    if (funOf(d) !== f) {
      allProven = false
      reports.push({name: d.name, kind: 'decision', proven: false, checked: false, why: `law was not stated on ${meta.name}`})
      continue
    }
    const v = proveDecision(d, opts.ms ? {ms: opts.ms} : {})
    const ok = v.proven && v.checked
    if (!ok) { allProven = false; firstFailed ??= v }
    reports.push({name: d.name, kind: 'decision', proven: v.proven, checked: v.checked, ...(v.goal ? {goal: v.goal} : {}), ...(v.why ? {why: v.why} : {})})
  }
  if (!allProven && !opts.allowUnproven) {
    throw new Unproven(
      laws.length === 0 ? `${meta.name}: no laws provided to prove` : `${meta.name}: not all laws are proven`,
      firstFailed ?? {proven: false, checked: false, why: laws.length === 0 ? 'no laws provided' : 'unproven law'},
    )
  }

  const m = meta.rule.machine
  const digest = machineDigest(m)
  const fnName = toCamel(opts.name ?? meta.name)
  const hasParams = meta.params.length > 0

  const decPlaces = new Set<number>()
  const roundedPlaces = new Set<number>()
  for (const [, , k] of [...meta.params, ...meta.inputs, ...meta.outputs]) {
    decimalPlacesIn(k, decPlaces)
    decimalRoundedPlacesIn(k, roundedPlaces)
  }
  const hasDecimals = decPlaces.size > 0

  const fnNames = new Map<string, string>()
  const fnHelperLines: string[] = []
  for (const [k, fn] of Object.entries(m.fns ?? {})) {
    if (/^(div|mod)\$\d+$/.test(k)) continue
    const d = directOf(fn)
    if (d?.kind === 'div' || d?.kind === 'mod' || d?.kind === 'const') continue
    const id = safeVar('$fn_', k)
    fnNames.set(k, id)
    fnHelperLines.push(...emitRuleFnHelper(id, fn))
  }

  const reg = makeRegistry()
  const scaleLines: string[] = []
  const helpers = new Set<'glob' | 'cpair' | 'cunpair' | 'dec' | 'decRound' | 'idx'>()

  // Register params & inputs; top-level decimal fields get clean scaled locals (e.g. `const $p_approveAt = $dec(...)`)
  for (const [n, , k] of meta.params) {
    if (k.kind === 'decimal') {
      const local = safeVar('$p_', n)
      if (k.round === 'half-even') {
        helpers.add('decRound')
        scaleLines.push(`  const ${local} = $decRound(${propAccess('params', n)}, ${k.places}, ${JSON.stringify(n)})`)
      } else {
        helpers.add('dec')
        scaleLines.push(`  const ${local} = $dec(${propAccess('params', n)}, ${k.places}, ${10 ** k.places}, ${JSON.stringify(n)})`)
      }
      registerKind(reg, n, k, local)
    } else {
      registerKind(reg, n, k, propAccess('params', n))
    }
  }
  for (const [n, , k] of meta.inputs) {
    if (k.kind === 'decimal') {
      const local = safeVar('$a_', n)
      if (k.round === 'half-even') {
        helpers.add('decRound')
        scaleLines.push(`  const ${local} = $decRound(${propAccess('args', n)}, ${k.places}, ${JSON.stringify(n)})`)
      } else {
        helpers.add('dec')
        scaleLines.push(`  const ${local} = $dec(${propAccess('args', n)}, ${k.places}, ${10 ** k.places}, ${JSON.stringify(n)})`)
      }
      registerKind(reg, n, k, local)
    } else {
      registerKind(reg, n, k, propAccess('args', n))
    }
  }

  const ctx: EmitCtx = {reg, flags: new Map(), maps: new Map(), fns: m.fns ?? {}, helpers, fnNames, boundKeys: new Map(), cse: new Map()}
  const em = emitTsCode(ctx)

  const paramChecks = meta.params.flatMap(([n, , k]) => kindGuardChecks(k, propAccess('params', n)))
  const inputChecks = meta.inputs.flatMap(([n, , k]) => kindGuardChecks(k, propAccess('args', n)))
  const preExpr = m.pre ? em.emitCond(m.pre) : 'true'
  const assumeExpr = m.assume ? em.emitCond(m.assume) : 'true'

  const flagLines: string[] = []
  for (const [fname, fc] of Object.entries(m.step.flags ?? {})) {
    const local = safeVar('$flag_', fname)
    flagLines.push(`  const ${local}: boolean = ${em.emitCond(fc)}`)
    ctx.flags.set(fname, local)
  }

  const outLocals: string[] = []
  const outFields: [string, string][] = []
  for (const [n, , k] of meta.outputs) {
    const val = em.emitKindVal(k, `out.${n}`, part => m.step.state?.[part] ?? m.state[part] ?? {op: 'const', value: 0})
    const finalExpr = k.kind === 'decimal' ? `(${val}) / ${10 ** k.places}` : val
    if (meta.outputs.length > 1) {
      const local = PLAIN_IDENT.test(n) && !RESERVED_IDENT.has(n) && n !== 'args' && n !== 'params' ? n : safeVar('$out_', n)
      outLocals.push(`  const ${local}: ${kindTsType(k)} = ${finalExpr}`)
      if (k.kind === 'oneOf' || k.kind === 'bool' || k.kind === 'nat') {
        const rawE = m.step.state?.[`out.${n}`]
        if (rawE) ctx.cse.set(JSON.stringify(rawE), {ts: local, kind: k})
      }
      outFields.push([n, local])
    } else {
      outFields.push([n, finalExpr])
    }
  }

  const placesList = [...decPlaces].sort((a, b) => a - b)
  const roundedList = [...roundedPlaces].sort((a, b) => a - b)
  const arithDesc = roundedList.length > 0
    ? `exact scaled fixed-point integers (${placesList.map(p => `10^-${p}`).join(', ')}); inputs rounded half-even to ${roundedList.map(p => `10^-${p}`).join(', ')}; laws hold for the rounded values; safe integer range <= 2^53 - 1`
    : hasDecimals
      ? `exact scaled fixed-point integers (${placesList.map(p => `10^-${p}`).join(', ')}); throws RangeError on inputs exceeding ${placesList.join('/')} decimal places (matching encodeInput); safe integer range <= 2^53 - 1`
      : 'exact JavaScript safe integers over N/Z (truncated natural subtraction max(0, a - b); safe range <= 2^53 - 1)'

  const lines: string[] = [
    ...renderHeader({name: meta.name, kind: 'fun', digest, arithmetic: arithDesc, laws: reports, ...(opts.provenance ? {provenance: opts.provenance} : {})}),
    '',
  ]
  if (hasParams) {
    lines.push('export type Params = {')
    for (const [n, , k] of meta.params) lines.push(`  readonly ${propKey(n)}: ${kindTsType(k)}`)
    lines.push('}', '')
  }
  lines.push('export type Input = {')
  for (const [n, , k] of meta.inputs) lines.push(`  readonly ${propKey(n)}: ${kindTsType(k)}`)
  lines.push('}', '')
  lines.push('export type Result = {')
  for (const [n, , k] of meta.outputs) lines.push(`  readonly ${propKey(n)}: ${kindTsType(k)}`)
  lines.push('}', '')

  const helperLines = renderHelpers(ctx.helpers)
  if (helperLines.length) lines.push(...helperLines, '')
  if (fnHelperLines.length) lines.push(...fnHelperLines, '')

  if (hasParams && opts.defaultParams) {
    lines.push('export function defaultParams(): Params {', '  return {')
    for (const [n] of meta.params) lines.push(`    ${propKey(n)}: ${JSON.stringify(opts.defaultParams[n])},`)
    lines.push('  }', '}', '')
  }

  const bodyLines: string[] = []
  for (const chk of paramChecks) bodyLines.push(`  if (${chk}) throw new RangeError(${JSON.stringify(`${meta.name}: invalid params`)})`)
  for (const chk of inputChecks) bodyLines.push(`  if (${chk}) throw new RangeError(${JSON.stringify(`${meta.name}: invalid input`)})`)
  bodyLines.push(...scaleLines)
  if (preExpr !== 'true') bodyLines.push(`  if (!(${preExpr})) throw new RangeError(${JSON.stringify(`${meta.name}: params violate precondition`)})`)
  bodyLines.push(...flagLines)
  if (assumeExpr !== 'true') bodyLines.push(`  if (!(${assumeExpr})) throw new RangeError(${JSON.stringify(`${meta.name}: input violates assumption`)})`)
  bodyLines.push(...outLocals)
  if (outFields.length === 1) {
    bodyLines.push(`  return { ${propKey(outFields[0]![0])}: ${outFields[0]![1]} }`)
  } else {
    bodyLines.push('  return {')
    for (const [n, expr] of outFields) {
      bodyLines.push(PLAIN_IDENT.test(n) && expr === n ? `    ${n},` : `    ${propKey(n)}: ${expr},`)
    }
    bodyLines.push('  }')
  }

  const sig = hasParams
    ? (opts.defaultParams ? '(args: Input, params: Params = defaultParams()): Result' : '(args: Input, params: Params): Result')
    : '(args: Input): Result'
  lines.push(`export function ${fnName}${sig} {`, ...bodyLines, '}', '')

  return {
    source: lines.join('\n'),
    digest,
    version: GDP_WIRED_VERSION,
    name: meta.name,
    kind: 'fun',
    exportName: fnName,
    laws: reports,
    allProven,
  }
}

// --- emitRule & emitChart --------------------------------------------------------------------------------------------

export function emitRule(r: AnyRule, opts: EmitRuleOptions = {}): EmitResult {
  return emitRuleInternal(r, opts, 'rule')
}

export function emitChart(c: AnyChart, opts: EmitChartOptions = {}): EmitResult {
  const {ownedLaws, ownedStepLaws} = inspectChart(c)
  const userLaws = opts.laws ? [...opts.laws] : ownedLaws
  const userSteps = opts.stepLaws ? [...opts.stepLaws] : ownedStepLaws
  const laws = [...c.chartLaws(), ...userLaws]
  return emitRuleInternal(c.rule, {...opts, laws, stepLaws: userSteps}, 'chart')
}

function emitRuleInternal(r: AnyRule, opts: EmitRuleOptions, kind: 'rule' | 'chart'): EmitResult {
  const meta: RuleMeta = inspectRuleMeta(r)
  const laws = opts.laws !== undefined ? [...opts.laws] : meta.ownedLaws
  const stepLaws = opts.stepLaws !== undefined ? [...opts.stepLaws] : meta.ownedStepLaws
  const proveOpts: ProveOptions = {
    ...(opts.prove ?? {}),
    ...(opts.from ? {from: opts.from} : {}),
    ...(opts.ms !== undefined ? {search: {ms: opts.ms}} : {}),
  }

  const reports: EmitLawReport[] = []
  let allProven = laws.length + stepLaws.length > 0
  let failedVerdict: Verdict | undefined

  if (allProven) {
    const v = stepLaws.length > 0 ? proveSteps(r, laws, stepLaws, proveOpts) : proveRule(r, laws, proveOpts)
    const assumesList = v.assumes?.laws
    const ok = v.proven && v.checked && !(opts.from === 'any' && assumesList?.length)
    if (!ok) { allProven = false; failedVerdict = v }
    for (const l of laws) {
      reports.push({
        name: l.name,
        kind: 'law',
        proven: ok,
        checked: ok && v.checked,
        ...(assumesList?.length ? {assumes: assumesList} : {}),
        ...(!ok && v.goal ? {goal: v.goal} : {}),
        ...(!ok && v.why ? {why: v.why} : {}),
      })
    }
    for (const sl of stepLaws) {
      reports.push({
        name: sl.name,
        kind: 'step',
        proven: ok,
        checked: ok && v.checked,
        ...(assumesList?.length ? {assumes: assumesList} : {}),
        ...(!ok && v.goal ? {goal: v.goal} : {}),
        ...(!ok && v.why ? {why: v.why} : {}),
      })
    }
  }

  if (!allProven && !opts.allowUnproven) {
    throw new Unproven(
      laws.length + stepLaws.length === 0 ? `${meta.name}: no laws provided to prove` : `${meta.name}: not all laws are proven`,
      failedVerdict ?? {proven: false, checked: false, why: laws.length + stepLaws.length === 0 ? 'no laws provided' : 'unproven law'},
    )
  }

  const m = r.machine
  const digest = machineDigest(m)
  const hasParams = meta.params.length > 0
  const hasInputs = meta.inputs.length > 0

  const decPlaces = new Set<number>()
  const roundedPlaces = new Set<number>()
  for (const [, , k] of [...meta.params, ...meta.inputs]) {
    decimalPlacesIn(k, decPlaces)
    decimalRoundedPlacesIn(k, roundedPlaces)
  }
  for (const [, k] of meta.state) { decimalPlacesIn(k, decPlaces); decimalRoundedPlacesIn(k, roundedPlaces) }
  for (const [, , k] of meta.maps) if (k) { decimalPlacesIn(k, decPlaces); decimalRoundedPlacesIn(k, roundedPlaces) }
  const hasDecimals = decPlaces.size > 0

  const fnNames = new Map<string, string>()
  const fnHelperLines: string[] = []
  for (const [k, fn] of Object.entries(m.fns ?? {})) {
    if (/^(div|mod)\$\d+$/.test(k)) continue
    const d = directOf(fn)
    if (d?.kind === 'div' || d?.kind === 'mod' || d?.kind === 'const') continue
    const id = safeVar('$fn_', k)
    fnNames.set(k, id)
    fnHelperLines.push(...emitRuleFnHelper(id, fn))
  }

  const helpers = new Set<'glob' | 'cpair' | 'cunpair' | 'dec' | 'decRound' | 'idx'>()
  const initScaleLines: string[] = []
  const stepScaleLines: string[] = []
  const reg = makeRegistry()
  const initReg = makeRegistry()
  for (const [n, , k] of meta.params) {
    if (k.kind === 'decimal') {
      const local = safeVar('$p_', n)
      const call = k.round === 'half-even'
        ? (helpers.add('decRound'), `$decRound(${propAccess('params', n)}, ${k.places}, ${JSON.stringify(n)})`)
        : (helpers.add('dec'), `$dec(${propAccess('params', n)}, ${k.places}, ${10 ** k.places}, ${JSON.stringify(n)})`)
      initScaleLines.push(`  const ${local} = ${call}`)
      stepScaleLines.push(`  const ${local} = ${call}`)
      registerKind(reg, n, k, local)
      registerKind(initReg, n, k, local)
    } else {
      registerKind(reg, n, k, propAccess('params', n))
      registerKind(initReg, n, k, propAccess('params', n))
    }
  }
  for (const [n, , k] of meta.inputs) {
    if (k.kind === 'decimal') {
      const local = safeVar('$i_', n)
      const call = k.round === 'half-even'
        ? (helpers.add('decRound'), `$decRound(${propAccess('input', n)}, ${k.places}, ${JSON.stringify(n)})`)
        : (helpers.add('dec'), `$dec(${propAccess('input', n)}, ${k.places}, ${10 ** k.places}, ${JSON.stringify(n)})`)
      stepScaleLines.push(`  const ${local} = ${call}`)
      registerKind(reg, n, k, local)
    } else {
      registerKind(reg, n, k, propAccess('input', n))
    }
  }
  for (const [n, k] of meta.state) {
    if (k.kind === 'decimal') {
      const local = safeVar('$s_', n)
      helpers.add('dec')
      stepScaleLines.push(`  const ${local} = $dec(${propAccess('state', n)}, ${k.places}, ${10 ** k.places}, ${JSON.stringify(n)})`)
      registerKind(reg, n, k, local)
    } else {
      registerKind(reg, n, k, propAccess('state', n))
    }
  }

  const eachMaps = new Set<string>()
  for (const [rawMap, w] of Object.entries(m.step.maps ?? {})) if ('each' in w) eachMaps.add(rawMap)

  const ctxMaps = new Map<string, MapInfo>()
  const cellGetters: string[] = []

  for (const [mapName, dflt, cellKind] of meta.maps) {
    if (!cellKind) {
      ctxMaps.set(mapName, {
        rawName: mapName,
        mapName,
        stateExpr: propAccess('state', mapName),
        defaultVal: dflt,
        fieldKind: {kind: 'nat'},
        ...(eachMaps.has(mapName) ? {dynamicDefaultExpr: propAccess('state', `${mapName}_default`)} : {}),
      })
    } else if (cellKind.kind === 'record') {
      const def = kindDefaultTs(cellKind)
      for (const [f, fk] of cellKind.fields) {
        const raw = `${mapName}.${f}`
        ctxMaps.set(raw, {
          rawName: raw,
          mapName,
          stateExpr: propAccess('state', mapName),
          defaultVal: m.maps?.[raw] ?? 0,
          fieldKind: fk,
          getterTpl: `((${propAccess('state', mapName)}.get(__K__) ?? ${def}).${f})`,
        })
      }
    } else if (cellKind.kind === 'variant') {
      const def = kindDefaultTs(cellKind)
      ctxMaps.set(mapName, {
        rawName: mapName,
        mapName,
        stateExpr: propAccess('state', mapName),
        defaultVal: 0,
        fieldKind: cellKind,
        dynamicDefaultExpr: def,
      })
      for (const [c, fs] of cellKind.cases) {
        for (const [f, fk] of fs) {
          const raw = `${mapName}.${c}.${f}`
          const gid = safeVar('$get_', raw)
          ctxMaps.set(raw, {
            rawName: raw,
            mapName,
            stateExpr: propAccess('state', mapName),
            defaultVal: m.maps?.[raw] ?? 0,
            fieldKind: fk,
            getterTpl: `${gid}(${propAccess('state', mapName)}, __K__)`,
          })
          cellGetters.push(
            `function ${gid}(m: ReadonlyMap<number, ${kindTsType(cellKind)}>, k: number): ${kindTsType(fk)} {`,
            '  const c = m.get(k)',
            `  return c !== undefined && ${propAccess('c', cellKind.tagKey)} === ${JSON.stringify(c)} ? ${propAccess('c', f)} : ${kindDefaultTs(fk)}`,
            '}',
          )
        }
      }
    }
  }

  for (const [itemName, itemKind] of meta.items) {
    reg.slots.set(`${itemName}_len`, {kind: 'nat', ts: `${propAccess('state', itemName)}.length`})
    if (itemKind.kind === 'record') {
      for (const [f, fk] of itemKind.fields) {
        const raw = `${itemName}.${f}`
        const gid = safeVar('$item_', raw)
        ctxMaps.set(raw, {rawName: raw, mapName: itemName, stateExpr: propAccess('state', itemName), defaultVal: 0, fieldKind: fk, getterTpl: `${gid}(${propAccess('state', itemName)}, __K__)`})
        cellGetters.push(
          `function ${gid}(xs: readonly ${kindTsType(itemKind)}[], k: number): ${kindTsType(fk)} {`,
          '  const c = xs[k]',
          `  return c !== undefined ? ${propAccess('c', f)} : ${kindDefaultTs(fk)}`,
          '}',
        )
      }
    } else {
      const gid = safeVar('$item_', itemName)
      ctxMaps.set(itemName, {rawName: itemName, mapName: itemName, stateExpr: propAccess('state', itemName), defaultVal: 0, fieldKind: itemKind, getterTpl: `${gid}(${propAccess('state', itemName)}, __K__)`})
      cellGetters.push(
        `function ${gid}(xs: readonly ${kindTsType(itemKind)}[], k: number): ${kindTsType(itemKind)} {`,
        `  return xs[k] ?? ${kindDefaultTs(itemKind)}`,
        '}',
      )
    }
  }

  const ctx: EmitCtx = {reg, flags: new Map(), maps: ctxMaps, fns: m.fns ?? {}, helpers, fnNames, boundKeys: new Map(), cse: new Map()}
  const em = emitTsCode(ctx)

  const initCtx: EmitCtx = {...ctx, reg: initReg, flags: new Map(), maps: new Map(), cse: new Map()}
  const initEm = emitTsCode(initCtx)

  const paramChecks = meta.params.flatMap(([n, , k]) => kindGuardChecks(k, propAccess('params', n)))
  const preExpr = m.pre ? initEm.emitCond(m.pre) : 'true'
  const inputChecks = meta.inputs.flatMap(([n, , k]) => kindGuardChecks(k, propAccess('input', n)))

  const historyFields = m.history ? {
    recordFields: m.history.record,
    sums: Object.entries(m.history.sums),
    queries: Object.entries(m.history.queries),
    keep: m.history.keep,
    prune: m.history.prune,
  } : undefined

  if (historyFields) {
    for (const [qName] of historyFields.queries) reg.slots.set(qName, {kind: 'nat', ts: safeVar('$q_', qName)})
  }

  const flagLines: string[] = []
  for (const [fname, fc] of Object.entries(m.step.flags ?? {})) {
    const local = safeVar('$flag_', fname)
    flagLines.push(`  const ${local}: boolean = ${em.emitCond(fc)}`)
    ctx.flags.set(fname, local)
  }

  const assumeExpr = m.assume ? em.emitCond(m.assume) : 'true'
  const primFailExpr = m.primitiveFailure ? em.emitCond(m.primitiveFailure) : undefined

  const nextScalars: [string, string][] = []
  for (const [n, k] of meta.state) {
    if (historyFields && historyFields.sums.some(([sn]) => sn === n)) continue
    const rawVal = em.emitKindVal(k, n, part => m.step.state?.[part] ?? {op: 'var', name: part})
    const val = k.kind === 'decimal' ? `(${rawVal}) / ${10 ** k.places}` : rawVal
    nextScalars.push([n, val])
    if (k.kind === 'oneOf' || k.kind === 'bool' || k.kind === 'nat') {
      const rawE = m.step.state?.[n]
      if (rawE) ctx.cse.set(JSON.stringify(rawE), {ts: safeVar('next_', n), kind: k})
    }
  }

  const mapUpdateLines: string[] = []
  const nextMapFields: [string, string][] = []
  for (const [mapName, , cellKind] of meta.maps) {
    const localMap = safeVar('next_', mapName)
    if (!cellKind) {
      const w = m.step.maps?.[mapName]
      if (!w) {
        nextMapFields.push([mapName, `new Map(${propAccess('state', mapName)})`])
      } else if ('each' in w) {
        const localDef = safeVar('nextDef_', mapName)
        ctx.boundKeys.set(w.each, '$k')
        const valAtK = em.emitNum(w.value)
        ctx.boundKeys.delete(w.each)
        mapUpdateLines.push(
          `  const ${localMap} = new Map<number, number>()`,
          `  let $past_${mapName} = 0`,
          `  for (const $k of ${propAccess('state', mapName)}.keys()) if ($k + 1 > $past_${mapName}) $past_${mapName} = $k + 1`,
          `  const ${localDef} = (($k: number) => ${valAtK})($past_${mapName})`,
          `  for (const $k of ${propAccess('state', mapName)}.keys()) {`,
          `    const $v = ${valAtK}`,
          `    if ($v !== ${localDef}) ${localMap}.set($k, $v)`,
          '  }',
        )
        nextMapFields.push([mapName, localMap], [`${mapName}_default`, localDef])
      } else {
        const kExpr = em.emitNum(w.key)
        mapUpdateLines.push(`  const ${localMap} = new Map(${propAccess('state', mapName)})`)
        if (w.value.op === 'if' && w.value.else.op === 'get' && w.value.else.map === mapName && sameNode(w.value.else.key, w.key)) {
          mapUpdateLines.push(`  if (${em.emitCond(w.value.c)}) { ${localMap}.set(${kExpr}, ${em.emitNum(w.value.then)}) }`)
        } else {
          mapUpdateLines.push(`  ${localMap}.set(${kExpr}, ${em.emitNum(w.value)})`)
        }
        nextMapFields.push([mapName, localMap])
      }
    } else if (cellKind.kind === 'record') {
      const partWrites = cellKind.fields.map(([f]) => [f, m.step.maps?.[`${mapName}.${f}`]] as const).filter(([, w]) => w !== undefined)
      if (!partWrites.length) {
        nextMapFields.push([mapName, `new Map(${propAccess('state', mapName)})`])
      } else {
        const firstW = partWrites[0]![1]!
        if ('each' in firstW) throw new Error(`emit: broadcast write on record map ${mapName} is not supported yet`)
        const kExpr = em.emitNum(firstW.key)
        const recVal = em.emitKindVal(cellKind, mapName, part => {
          const pw = m.step.maps?.[part]
          return pw && 'key' in pw ? pw.value : {op: 'get', map: part, key: firstW.key}
        })
        mapUpdateLines.push(`  const ${localMap} = new Map(${propAccess('state', mapName)})`, `  ${localMap}.set(${kExpr}, ${recVal})`)
        nextMapFields.push([mapName, localMap])
      }
    } else if (cellKind.kind === 'variant') {
      const tagW = m.step.maps?.[mapName]
      if (!tagW) {
        nextMapFields.push([mapName, `new Map(${propAccess('state', mapName)})`])
      } else if ('each' in tagW) {
        throw new Error(`emit: broadcast write on variant map ${mapName} is not supported yet`)
      } else {
        const kExpr = em.emitNum(tagW.key)
        const varVal = em.emitKindVal(cellKind, mapName, part => {
          const pw = m.step.maps?.[part]
          return pw && 'key' in pw ? pw.value : {op: 'get', map: part, key: tagW.key}
        })
        mapUpdateLines.push(`  const ${localMap} = new Map(${propAccess('state', mapName)})`, `  ${localMap}.set(${kExpr}, ${varVal})`)
        nextMapFields.push([mapName, localMap])
      }
    }
  }

  const itemUpdateLines: string[] = []
  const nextItemFields: [string, string][] = []
  for (const [itemName, itemKind] of meta.items) {
    const localList = safeVar('next_', itemName)
    const lenE = m.step.state?.[`${itemName}_len`] ?? {op: 'var', name: `${itemName}_len`}
    const nextLenExpr = em.emitNum(lenE)
    const partNames = itemKind.kind === 'record' ? itemKind.fields.map(([f]) => `${itemName}.${f}`) : [itemName]
    const firstW = partNames.map(p => m.step.maps?.[p]).find(Boolean)
    if (firstW && 'each' in firstW) {
      const boundNames: string[] = []
      for (const p of partNames) {
        const pw = m.step.maps?.[p]
        if (pw && 'each' in pw) { ctx.boundKeys.set(pw.each, '$k'); boundNames.push(pw.each) }
      }
      const valExpr = em.emitKindVal(itemKind, itemName, part => {
        const pw = m.step.maps?.[part]
        return pw && 'each' in pw ? pw.value : {op: 'get', map: part, key: {op: 'var', name: firstW.each}}
      })
      for (const bn of boundNames) ctx.boundKeys.delete(bn)
      itemUpdateLines.push(
        `  const $len_${itemName} = ${nextLenExpr}`,
        `  const ${localList}: ${kindTsType(itemKind)}[] = []`,
        `  for (let $k = 0; $k < $len_${itemName}; $k++) { ${localList}.push(${valExpr}) }`,
      )
    } else if (firstW && 'key' in firstW) {
      itemUpdateLines.push(`  const ${localList} = [...${propAccess('state', itemName)}]`)
      const kExpr = em.emitNum(firstW.key)
      const valExpr = em.emitKindVal(itemKind, itemName, part => {
        const pw = m.step.maps?.[part]
        return pw && 'key' in pw ? pw.value : {op: 'get', map: part, key: firstW.key}
      })
      itemUpdateLines.push(
        `  const $len_${itemName} = ${nextLenExpr}`,
        `  const $idx_${itemName} = ${kExpr}`,
        `  if ($len_${itemName} > ${localList}.length) { ${localList}.push(${valExpr}) }`,
        `  else if ($len_${itemName} < ${localList}.length) { ${localList}.length = $len_${itemName} }`,
        `  else if ($idx_${itemName} < ${localList}.length) { ${localList}[$idx_${itemName}] = ${valExpr} }`,
      )
    } else {
      itemUpdateLines.push(`  const ${localList} = [...${propAccess('state', itemName)}]`, `  ${localList}.length = ${nextLenExpr}`)
    }
    nextItemFields.push([itemName, localList])
  }

  const historyLines: string[] = []
  const nextHistoryFields: [string, string][] = []
  if (historyFields) {
    const recReg = makeRegistry()
    for (const [n, , k] of meta.params) registerKind(recReg, n, k, propAccess('params', n))
    for (const [n, , k] of meta.inputs) registerKind(recReg, n, k, propAccess('input', n))
    for (const rf of historyFields.recordFields) {
      const k = meta.inputs.find(([n]) => n === rf)?.[2] ?? {kind: 'nat' as const}
      registerKind(recReg, `r.${rf}`, k, propAccess('$rec', rf))
    }
    const recEm = emitTsCode({...ctx, reg: recReg, flags: new Map(), maps: new Map(), cse: new Map()})
    if (historyFields.prune) {
      const ord = historyFields.prune.order
      const afterExpr = recEm.emitNum(historyFields.prune.after)
      historyLines.push(
        `  if (${propAccess('input', ord)} < state._last) throw new RangeError(${JSON.stringify(`${meta.name}: request order went backwards`)})`,
        `  const $kept = state._history.filter($rec => ${propAccess('$rec', ord)} + (${afterExpr}) > ${propAccess('input', ord)})`,
      )
    } else {
      historyLines.push('  const $kept = [...state._history]')
    }
    for (const [qName, qE] of historyFields.queries) {
      historyLines.push(`  let ${safeVar('$q_', qName)} = 0`, `  for (const $rec of $kept) ${safeVar('$q_', qName)} += ${recEm.emitNum(qE)}`)
    }
    nextHistoryFields.push(['_history', '$nextHistory'])
    if (historyFields.prune) nextHistoryFields.push(['_last', propAccess('input', historyFields.prune.order)])
  }

  const placesList = [...decPlaces].sort((a, b) => a - b)
  const roundedList = [...roundedPlaces].sort((a, b) => a - b)
  const arithDesc = roundedList.length > 0
    ? `exact scaled fixed-point integers (${placesList.map(p => `10^-${p}`).join(', ')}); inputs rounded half-even to ${roundedList.map(p => `10^-${p}`).join(', ')}; laws hold for the rounded values; safe integer range <= 2^53 - 1`
    : hasDecimals
      ? `exact scaled fixed-point integers (${placesList.map(p => `10^-${p}`).join(', ')}); throws RangeError on inputs exceeding ${placesList.join('/')} decimal places (matching encodeInput); safe integer range <= 2^53 - 1`
      : 'exact JavaScript safe integers over N/Z (truncated natural subtraction max(0, a - b); safe range <= 2^53 - 1)'

  const lines: string[] = [
    ...renderHeader({name: meta.name, kind, digest, arithmetic: arithDesc, laws: reports, ...(opts.provenance ? {provenance: opts.provenance} : {})}),
    '',
  ]

  lines.push(hasParams ? `export type Params = {\n${meta.params.map(([n, , k]) => `  readonly ${propKey(n)}: ${kindTsType(k)}`).join('\n')}\n}` : 'export type Params = Record<string, never>', '')
  lines.push(hasInputs ? `export type Input = {\n${meta.inputs.map(([n, , k]) => `  readonly ${propKey(n)}: ${kindTsType(k)}`).join('\n')}\n}` : 'export type Input = Record<string, never>', '')

  if (historyFields) {
    lines.push('export type HistoryRecord = {')
    for (const rf of historyFields.recordFields) {
      const k = meta.inputs.find(([n]) => n === rf)?.[2] ?? {kind: 'nat' as const}
      lines.push(`  readonly ${propKey(rf)}: ${kindTsType(k)}`)
    }
    lines.push('}', '')
  }

  lines.push('export type State = {')
  for (const [n, k] of meta.state) lines.push(`  readonly ${propKey(n)}: ${kindTsType(k)}`)
  for (const [mapName, , cellKind] of meta.maps) {
    lines.push(`  readonly ${propKey(mapName)}: Map<number, ${cellKind ? kindTsType(cellKind) : 'number'}>`)
    if (!cellKind && eachMaps.has(mapName)) lines.push(`  readonly ${propKey(`${mapName}_default`)}: number`)
  }
  for (const [itemName, itemKind] of meta.items) lines.push(`  readonly ${propKey(itemName)}: readonly ${kindTsType(itemKind)}[]`)
  if (historyFields) {
    for (const [sName] of historyFields.sums) {
      if (!meta.state.some(([n]) => n === sName)) lines.push(`  readonly ${propKey(sName)}: number`)
    }
    lines.push('  readonly _history: readonly HistoryRecord[]')
    if (historyFields.prune) lines.push('  readonly _last: number')
  }
  lines.push('}', '')

  const helperLines = renderHelpers(ctx.helpers)
  if (helperLines.length) lines.push(...helperLines, '')
  if (fnHelperLines.length) lines.push(...fnHelperLines, '')
  if (cellGetters.length) lines.push(...cellGetters, '')

  // init(params)
  const initBodyLines: string[] = []
  if (paramChecks.length) initBodyLines.push(`  if (${paramChecks.join(' || ')}) throw new RangeError(${JSON.stringify(`${meta.name}: invalid params`)})`)
  initBodyLines.push(...initScaleLines)
  if (preExpr !== 'true') initBodyLines.push(`  if (!(${preExpr})) throw new RangeError(${JSON.stringify(`${meta.name}: params violate precondition`)})`)
  initBodyLines.push('  return {')
  for (const [n, k] of meta.state) {
    const rawInit = initEm.emitKindVal(k, n, part => m.state[part] ?? {op: 'const', value: 0})
    const initVal = k.kind === 'decimal' ? `(${rawInit}) / ${10 ** k.places}` : rawInit
    initBodyLines.push(`    ${propKey(n)}: ${initVal},`)
  }
  for (const [mapName, dflt, cellKind] of meta.maps) {
    initBodyLines.push(`    ${propKey(mapName)}: new Map(),`)
    if (!cellKind && eachMaps.has(mapName)) initBodyLines.push(`    ${propKey(`${mapName}_default`)}: ${dflt},`)
  }
  for (const [itemName] of meta.items) initBodyLines.push(`    ${propKey(itemName)}: [],`)
  if (historyFields) {
    for (const [sName] of historyFields.sums) {
      if (!meta.state.some(([n]) => n === sName)) initBodyLines.push(`    ${propKey(sName)}: 0,`)
    }
    initBodyLines.push('    _history: [],')
    if (historyFields.prune) initBodyLines.push('    _last: 0,')
  }
  initBodyLines.push('  }')
  const initUsesP = initBodyLines.some(l => /\bparams\b/.test(l))
  lines.push(`export function init(${hasParams ? (initUsesP ? 'params: Params' : '_params: Params') : '_params: Params = {}'}): State {`, ...initBodyLines, '}', '')

  // step(params, state, input)
  const stepBodyLines: string[] = []
  if (inputChecks.length) stepBodyLines.push(`  if (${inputChecks.join(' || ')}) throw new RangeError(${JSON.stringify(`${meta.name}: invalid input`)})`)
  stepBodyLines.push(...stepScaleLines, ...historyLines, ...flagLines)
  if (assumeExpr !== 'true') stepBodyLines.push(`  if (!(${assumeExpr})) throw new RangeError(${JSON.stringify(`${meta.name}: input violates assumption`)})`)
  if (primFailExpr && primFailExpr !== 'false') stepBodyLines.push(`  if (${primFailExpr}) throw new RangeError(${JSON.stringify(`${meta.name}: arithmetic trap`)})`)
  for (const [n, expr] of nextScalars) stepBodyLines.push(`  const ${safeVar('next_', n)} = ${expr}`)
  stepBodyLines.push(...mapUpdateLines, ...itemUpdateLines)

  if (historyFields) {
    const curReg = makeRegistry()
    for (const [n, , k] of meta.params) registerKind(curReg, n, k, propAccess('params', n))
    for (const [n, , k] of meta.inputs) registerKind(curReg, n, k, propAccess('input', n))
    for (const rf of historyFields.recordFields) {
      const k = meta.inputs.find(([n]) => n === rf)?.[2] ?? {kind: 'nat' as const}
      registerKind(curReg, `r.${rf}`, k, propAccess('input', rf))
    }
    const curEm = emitTsCode({...ctx, reg: curReg, flags: new Map(), maps: new Map(), cse: new Map()})
    const keepExpr = em.emitCond(historyFields.keep)
    const recObj = `{ ${historyFields.recordFields.map(rf => `${propKey(rf)}: ${propAccess('input', rf)}`).join(', ')} }`
    stepBodyLines.push(`  const $keep = ${keepExpr}`)
    stepBodyLines.push(`  const $nextHistory = $keep ? [...$kept, ${recObj}] : $kept`)
    for (const [sName, sE] of historyFields.sums) {
      stepBodyLines.push(`  const ${safeVar('next_', sName)} = ${propAccess('state', sName)} + ($keep ? ${curEm.emitNum(sE)} : 0)`)
      if (!meta.state.some(([n]) => n === sName)) nextHistoryFields.push([sName, safeVar('next_', sName)])
    }
  }

  stepBodyLines.push('  return {')
  for (const [n] of meta.state) stepBodyLines.push(`    ${propKey(n)}: ${safeVar('next_', n)},`)
  for (const [n, expr] of nextMapFields) stepBodyLines.push(`    ${propKey(n)}: ${expr},`)
  for (const [n, expr] of nextItemFields) stepBodyLines.push(`    ${propKey(n)}: ${expr},`)
  for (const [n, expr] of nextHistoryFields) stepBodyLines.push(`    ${propKey(n)}: ${expr},`)
  stepBodyLines.push('  }')

  const stepP = stepBodyLines.some(l => /\bparams\b/.test(l)) ? 'params: Params' : '_params: Params'
  const stepS = stepBodyLines.some(l => /\bstate\b/.test(l)) ? 'state: State' : '_state: State'
  const stepI = stepBodyLines.some(l => /\binput\b/.test(l)) ? 'input: Input' : '_input: Input'
  lines.push(`export function step(${stepP}, ${stepS}, ${stepI}): State {`, ...stepBodyLines, '}', '')

  return {
    source: lines.join('\n'),
    digest,
    version: GDP_WIRED_VERSION,
    name: meta.name,
    kind,
    exportName: 'step',
    laws: reports,
    allProven,
  }
}

// --- emitRatRule -----------------------------------------------------------------------------------------------------

export function emitRatRule(r: AnyRatRule, opts: EmitRatOptions = {}): EmitResult {
  const meta = inspectRatRule(r)
  const laws: QLaw[] = opts.laws ? [...opts.laws] : meta.ownedLaws
  const m = meta.machine
  const digest = qMachineDigest(m)
  const reports: EmitLawReport[] = []
  let allProven = laws.length > 0
  let failedWhy: string | undefined

  if (allProven) {
    const v = proveRatRule(r, laws, {...(opts.ms !== undefined ? {ms: opts.ms} : {}), ...(opts.depth !== undefined ? {depth: opts.depth} : {})})
    const ok = v.proven && v.checked
    if (!ok) { allProven = false; failedWhy = v.why ?? v.goal ?? 'not proven' }
    for (const l of laws) {
      reports.push({name: l.name, kind: 'law', proven: ok, checked: ok && v.checked, ...(!ok && v.goal ? {goal: v.goal} : {}), ...(!ok && v.why ? {why: v.why} : {})})
    }
  }

  if (!allProven && !opts.allowUnproven) {
    throw new Unproven(
      laws.length === 0 ? `${meta.name}: no laws provided to prove` : `${meta.name}: not all rational laws are proven`,
      {proven: false, checked: false, why: failedWhy ?? 'no laws provided'},
    )
  }

  const hasParams = meta.params.length > 0
  const hasInputs = meta.inputs.length > 0
  const paramSet = new Set(meta.params.map(([n]) => n))
  const inputSet = new Set(meta.inputs.map(([n]) => n))
  const stateSet = new Set(meta.state)

  const varTs = (name: string, scope: 'init' | 'step'): string => {
    if (paramSet.has(name)) return propAccess('params', name)
    if (scope === 'step' && inputSet.has(name)) return propAccess('input', name)
    if (scope === 'step' && stateSet.has(name)) return propAccess('state', name)
    return name
  }

  const emitQE = (t: QE, scope: 'init' | 'step'): string => {
    switch (t.op) {
      case 'var': return varTs(t.name, scope)
      case 'const': { const r0 = q(t.q.num, t.q.den); return `[${r0.num}n, ${r0.den}n]` }
      case 'add': return `$add(${emitQE(t.a, scope)}, ${emitQE(t.b, scope)})`
      case 'sub': return `$sub(${emitQE(t.a, scope)}, ${emitQE(t.b, scope)})`
      case 'mul': { const r0 = q(t.k.num, t.k.den); return `$mul([${r0.num}n, ${r0.den}n], ${emitQE(t.a, scope)})` }
      case 'min': return `$min(${emitQE(t.a, scope)}, ${emitQE(t.b, scope)})`
      case 'max': return `$max(${emitQE(t.a, scope)}, ${emitQE(t.b, scope)})`
      case 'if': return `(${emitQC(t.c, scope)} ? ${emitQE(t.then, scope)} : ${emitQE(t.else, scope)})`
    }
  }

  const emitQC = (t: QC, scope: 'init' | 'step'): string => {
    switch (t.op) {
      case '<=': return `($cmp(${emitQE(t.a, scope)}, ${emitQE(t.b, scope)}) <= 0)`
      case '<': return `($cmp(${emitQE(t.a, scope)}, ${emitQE(t.b, scope)}) < 0)`
      case '=': return `($cmp(${emitQE(t.a, scope)}, ${emitQE(t.b, scope)}) === 0)`
      case 'and': return `(${emitQC(t.a, scope)} && ${emitQC(t.b, scope)})`
      case 'or': return `(${emitQC(t.a, scope)} || ${emitQC(t.b, scope)})`
      case 'not': return `!(${emitQC(t.x, scope)})`
    }
  }

  const lines: string[] = [
    ...renderHeader({
      name: opts.name ?? meta.name,
      kind: 'ratRule',
      digest,
      arithmetic: 'exact rational arithmetic over Q using reduced [bigint, bigint] pairs (num, den > 0, gcd(|num|, den) = 1); zero floating-point rounding',
      laws: reports,
      ...(opts.provenance ? {provenance: opts.provenance} : {}),
    }),
    '',
    'export type Rat = readonly [bigint, bigint]',
    'export type RatInput = Rat | bigint | number | string',
    '',
    hasParams ? `export type Params = {\n${meta.params.map(([n]) => `  readonly ${propKey(n)}: Rat`).join('\n')}\n}` : 'export type Params = Record<string, never>',
    '',
    hasInputs ? `export type Input = {\n${meta.inputs.map(([n]) => `  readonly ${propKey(n)}: Rat`).join('\n')}\n}` : 'export type Input = Record<string, never>',
    '',
    `export type State = {\n${meta.state.map(n => `  readonly ${propKey(n)}: Rat`).join('\n')}\n}`,
    '',
    'function $gcd(a: bigint, b: bigint): bigint {',
    '  let x = a < 0n ? -a : a',
    '  let y = b < 0n ? -b : b',
    '  while (y !== 0n) { const t = x % y; x = y; y = t }',
    '  return x',
    '}',
    'function $rat(num: bigint, den: bigint = 1n): Rat {',
    "  if (den === 0n) throw new RangeError('rational denominator cannot be 0')",
    '  const n = den < 0n ? -num : num',
    '  const d = den < 0n ? -den : den',
    '  const g = $gcd(n, d) || 1n',
    '  return [n / g, d / g]',
    '}',
    'function $add(a: Rat, b: Rat): Rat { return $rat(a[0] * b[1] + b[0] * a[1], a[1] * b[1]) }',
    'function $sub(a: Rat, b: Rat): Rat { return $rat(a[0] * b[1] - b[0] * a[1], a[1] * b[1]) }',
    'function $mul(a: Rat, b: Rat): Rat { return $rat(a[0] * b[0], a[1] * b[1]) }',
    'function $cmp(a: Rat, b: Rat): number { const d = a[0] * b[1] - b[0] * a[1]; return d < 0n ? -1 : d > 0n ? 1 : 0 }',
    'function $min(a: Rat, b: Rat): Rat { return $cmp(a, b) <= 0 ? a : b }',
    'function $max(a: Rat, b: Rat): Rat { return $cmp(a, b) <= 0 ? b : a }',
    '',
    'export function toRat(x: RatInput): Rat {',
    '  if (Array.isArray(x)) return $rat(x[0], x[1])',
    "  if (typeof x === 'bigint') return [x, 1n]",
    "  if (typeof x === 'number' && !Number.isFinite(x)) throw new RangeError(`invalid rational ${x}`)",
    '  const text = String(x).trim()',
    '  const frac = /^(-?\\d+)\\s*\\/\\s*(\\d+)$/.exec(text)',
    '  if (frac) return $rat(BigInt(frac[1]!), BigInt(frac[2]!))',
    '  const m = /^(-?)(\\d*)(?:\\.(\\d*))?(?:e([+-]?\\d+))?$/i.exec(text)',
    '  if (!m || (!m[2] && !m[3])) throw new RangeError(`invalid rational ${text}`)',
    "  const digits = BigInt(`${m[2] || '0'}${m[3] ?? ''}`)",
    '  const exp = Number(m[4] ?? 0) - (m[3]?.length ?? 0)',
    '  const v = exp >= 0 ? $rat(digits * 10n ** BigInt(exp), 1n) : $rat(digits, 10n ** BigInt(-exp))',
    '  return m[1] ? [-v[0], v[1]] : v',
    '}',
    '',
    'export function formatRat(r: Rat): string {',
    '  return r[1] === 1n ? String(r[0]) : `${String(r[0])}/${String(r[1])}`',
    '}',
    '',
  ]

  // init
  const initBody: string[] = []
  const preCheck = m.pre ? emitQC(m.pre, 'init') : undefined
  if (preCheck) initBody.push(`  if (!(${preCheck})) throw new RangeError(${JSON.stringify(`${meta.name}: params violate precondition`)})`)
  initBody.push('  return {')
  for (const s of meta.state) initBody.push(`    ${propKey(s)}: ${emitQE(m.state[s]!, 'init')},`)
  initBody.push('  }')
  const initSig = hasParams ? (initBody.some(l => /\bparams\b/.test(l)) ? 'params: Params' : '_params: Params') : '_params: Params = {}'
  lines.push(`export function init(${initSig}): State {`, ...initBody, '}', '')

  // allowed
  const allowExpr = m.assume ? emitQC(m.assume, 'step') : 'true'
  const allowP = /\bparams\b/.test(allowExpr) ? 'params: Params' : '_params: Params'
  const allowS = /\bstate\b/.test(allowExpr) ? 'state: State' : '_state: State'
  const allowI = /\binput\b/.test(allowExpr) ? 'input: Input' : '_input: Input'
  lines.push(`export function allowed(${allowP}, ${allowS}, ${allowI}): boolean {`, `  return ${allowExpr}`, '}', '')

  // step
  const stepBody: string[] = []
  const stateFields = meta.state.map(s => `    ${propKey(s)}: ${m.step[s] ? emitQE(m.step[s]!, 'step') : propAccess('state', s)},`)
  const stepUsesP = stateFields.some(l => /\bparams\b/.test(l)) || !!m.assume
  const stepUsesS = stateFields.some(l => /\bstate\b/.test(l)) || !!m.assume
  const stepUsesI = stateFields.some(l => /\binput\b/.test(l)) || !!m.assume
  if (m.assume) stepBody.push(`  if (!allowed(params, state, input)) throw new RangeError(${JSON.stringify(`${meta.name}: input violates assumption`)})`)
  stepBody.push('  return {', ...stateFields, '  }')
  lines.push(`export function step(${stepUsesP ? 'params: Params' : '_params: Params'}, ${stepUsesS ? 'state: State' : '_state: State'}, ${stepUsesI ? 'input: Input' : '_input: Input'}): State {`, ...stepBody, '}', '')

  const rawSource = lines.join('\n')
  const cleanedLines = lines.filter(line => {
    const fm = /^function (\$(?:add|sub|mul|cmp|min|max))\b/.exec(line)
    if (!fm) return true
    return rawSource.split(fm[1]!).length - 1 > 1
  })

  return {
    source: cleanedLines.join('\n'),
    digest,
    version: GDP_WIRED_VERSION,
    name: meta.name,
    kind: 'ratRule',
    exportName: 'step',
    laws: reports,
    allProven,
  }
}
