// Emit self-contained, zero-dependency TypeScript source from proven gdp-wired rules, functions, rational rules and
// statecharts. Generated code has zero imports, zero dynamic code generation, and zero proof/kernel runtime.
// When the rule sits inside the TypeScript reader's subset, emitted files also carry `// gdp: law` comments so
// `gdp-wired emit --verify` (or `gdp-wired check`) closes the loop by re-proving the generated code directly.
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
  funSymbolicLaw,
  inspectFunMeta,
  inspectRuleMeta,
  interned,
  proveDecision,
  proveRule,
  proveSteps,
} from './dsl.ts'
import {type RatLaw, type RatRule, inspectRatRule, proveRatRule} from './rationals.ts'
import {type Chart, inspectChart} from './chart.ts'
import {q} from './q.ts'

export const GDP_WIRED_VERSION = '0.61.0'

export type EmitLawReport = {
  readonly name: string
  readonly kind: 'law' | 'step' | 'decision'
  readonly proven: boolean
  readonly checked: boolean
  readonly assumes?: readonly string[]
  readonly goal?: string
  readonly why?: string
  readonly lawExpr?: string
}

export type EmitVerifyInfo = {
  readonly verifiable: boolean
  readonly entry?: string
  readonly mode?: 'standalone'
  readonly from?: 'any'
  readonly expectedLaws: readonly string[]
  readonly reasons: readonly string[]
}

export type EmitResult = {
  readonly source: string
  readonly digest: string
  readonly version: string
  readonly name: string
  readonly kind: 'rule' | 'fun' | 'ratRule' | 'chart'
  readonly laws: readonly EmitLawReport[]
  readonly allProven: boolean
  readonly verify: EmitVerifyInfo
}

export type EmitRuleOptions = {
  laws?: readonly Law[]
  stepLaws?: readonly StepLaw[]
  name?: string
  from?: 'any'
  ms?: number
  prove?: ProveOptions
  allowUnproven?: boolean
}

export type EmitFunOptions = {
  laws?: readonly Decision[]
  name?: string
  defaultParams?: Readonly<Record<string, Raw>>
  ms?: number
  allowUnproven?: boolean
}

export type EmitRatOptions = {
  laws?: readonly RatLaw<string, string>[]
  name?: string
  ms?: number
  depth?: number
  allowUnproven?: boolean
}

export type EmitChartOptions = {
  laws?: readonly Law[]
  stepLaws?: readonly StepLaw[]
  name?: string
  from?: 'any'
  ms?: number
  prove?: ProveOptions
  allowUnproven?: boolean
}

export type EmitBundle =
  | {readonly rule: Rule<object, object, object, object, object, object, object, object>, readonly laws?: readonly Law[], readonly stepLaws?: readonly StepLaw[], readonly name?: string, readonly from?: 'any', readonly ms?: number}
  | {readonly fun: Fun<object, object, object>, readonly laws?: readonly Decision[], readonly name?: string, readonly defaultParams?: Readonly<Record<string, Raw>>, readonly ms?: number}
  | {readonly ratRule: RatRule<string, string, string>, readonly laws?: readonly RatLaw<string, string>[], readonly name?: string, readonly ms?: number}
  | {readonly chart: Chart<object, object, object>, readonly laws?: readonly Law[], readonly stepLaws?: readonly StepLaw[], readonly name?: string, readonly from?: 'any', readonly ms?: number}

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
  '__cov', '__now', '__gdp_tick', '$join',
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

function toPascal(name: string): string {
  const ws = wordsOf(name)
  let id = ws.map(w => w.charAt(0).toUpperCase() + w.slice(1)).join('')
  if (/^\d/.test(id)) id = `Rule${id}`
  if (RESERVED_IDENT.has(id)) id = `${id}Machine`
  return id
}

function propKey(k: string): string { return PLAIN_IDENT.test(k) ? k : JSON.stringify(k) }
function propAccess(base: string, k: string): string { return PLAIN_IDENT.test(k) ? `${base}.${k}` : `${base}[${JSON.stringify(k)}]` }
function safeVar(prefix: string, name: string): string { return `${prefix}${name.replace(/[^A-Za-z0-9_]/g, '_')}` }
function sanitizeComment(s: string): string {
  return s.replace(/[\r\n]+/g, ' ').replace(/\b(import|require|Function|eval)\b/g, w => `${w.slice(0, 1)}_${w.slice(1)}`)
}

// --- Kind TypeScript types, defaults & runtime guards ----------------------------------------------------------------

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

function hasDecimalKind(k: KindInfo): boolean {
  switch (k.kind) {
    case 'decimal': return true
    case 'maybe': return hasDecimalKind(k.of)
    case 'record': return k.fields.some(([, fk]) => hasDecimalKind(fk))
    case 'variant': return k.cases.some(([, fs]) => fs.some(([, fk]) => hasDecimalKind(fk)))
    default: return false
  }
}

function isSimpleReaderKind(k: KindInfo): boolean {
  return k.kind === 'nat' || k.kind === 'bool' || k.kind === 'oneOf' || k.kind === 'int'
}

function isStandaloneKind(k: KindInfo): boolean {
  return k.kind === 'nat' || k.kind === 'bool' || k.kind === 'oneOf' || k.kind === 'int' || k.kind === 'decimal'
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

function addLin(dst: LinForm, e: E, scale: number, signedVars: ReadonlySet<string>): void {
  if (scale === 0) return
  switch (e.op) {
    case 'const': dst.constVal += scale * e.value; return
    case 'var': dst.vars.set(e.name, (dst.vars.get(e.name) ?? 0) + scale); return
    case 'add': addLin(dst, e.a, scale, signedVars); addLin(dst, e.b, scale, signedVars); return
    case 'mul': addLin(dst, e.a, scale * e.k, signedVars); return
    default: dst.rest.push({coeff: scale, e})
  }
}

function cancelSigned(lin: LinForm, signedVars: ReadonlySet<string>): void {
  for (const name of signedVars) {
    const neg = `${name}$neg`
    const p = lin.vars.get(name) ?? 0
    const q = lin.vars.get(neg) ?? 0
    if (p === 0 || q === 0) continue
    if (p > 0 && q < 0) {
      const k = Math.min(p, -q)
      lin.vars.set(name, p - k)
      lin.vars.set(neg, q + k)
      lin.signed.set(name, (lin.signed.get(name) ?? 0) + k)
    } else if (p < 0 && q > 0) {
      const k = Math.min(-p, q)
      lin.vars.set(name, p + k)
      lin.vars.set(neg, q - k)
      lin.signed.set(name, (lin.signed.get(name) ?? 0) - k)
    }
  }
  for (const [k, v] of [...lin.vars]) if (v === 0) lin.vars.delete(k)
  for (const [k, v] of [...lin.signed]) if (v === 0) lin.signed.delete(k)
}

// --- Slot registration for Kind trees --------------------------------------------------------------------------------

type Slot =
  | {kind: 'nat', ts: string, law: string}
  | {kind: 'bool', ts: string, law: string}
  | {kind: 'oneOf', ts: string, law: string, values: readonly string[]}
  | {kind: 'intPos', ts: string, law: string, base: string}
  | {kind: 'intNeg', ts: string, law: string, base: string}
  | {kind: 'maybeSome', ts: string, law: string}
  | {kind: 'variantTag', ts: string, law: string, tagKey: string, cases: readonly string[]}
  | {kind: 'strId', ts: string, law: string, patterns: readonly string[]}
  | {kind: 'strLen', ts: string, law: string}
  | {kind: 'strLike', ts: string, law: string, pattern: string}

type SlotRegistry = {
  slots: Map<string, Slot>
  signedVars: Set<string>
  signedTs: Map<string, string>
  signedLaw: Map<string, string>
  strLiterals: Map<number, string>
}

function makeRegistry(): SlotRegistry {
  const strLiterals = new Map<number, string>()
  for (const [text, id] of interned()) strLiterals.set(id, text)
  return {slots: new Map(), signedVars: new Set(), signedTs: new Map(), signedLaw: new Map(), strLiterals}
}

function registerKind(reg: SlotRegistry, rawName: string, kind: KindInfo, tsExpr: string, lawExpr: string, guard?: {condTs: string, condLaw: string}): void {
  const wrapTs = (expr: string, fallback: string) => (guard ? `(${guard.condTs} ? ${expr} : ${fallback})` : expr)
  const wrapLaw = (expr: string) => expr
  switch (kind.kind) {
    case 'nat':
    case 'unknown':
      reg.slots.set(rawName, {kind: 'nat', ts: wrapTs(tsExpr, '0'), law: wrapLaw(lawExpr)})
      return
    case 'bool':
      reg.slots.set(rawName, {kind: 'bool', ts: wrapTs(tsExpr, 'false'), law: wrapLaw(lawExpr)})
      return
    case 'oneOf':
      reg.slots.set(rawName, {kind: 'oneOf', ts: wrapTs(tsExpr, JSON.stringify(kind.values[0]!)), law: wrapLaw(lawExpr), values: kind.values})
      return
    case 'int':
    case 'decimal':
      reg.signedVars.add(rawName)
      reg.signedTs.set(rawName, wrapTs(tsExpr, '0'))
      reg.signedLaw.set(rawName, wrapLaw(lawExpr))
      reg.slots.set(rawName, {kind: 'intPos', ts: wrapTs(tsExpr, '0'), law: wrapLaw(lawExpr), base: rawName})
      reg.slots.set(`${rawName}$neg`, {kind: 'intNeg', ts: wrapTs(tsExpr, '0'), law: wrapLaw(lawExpr), base: rawName})
      return
    case 'maybe': {
      reg.slots.set(`${rawName}$some`, {kind: 'maybeSome', ts: wrapTs(tsExpr, 'null'), law: wrapLaw(lawExpr)})
      const innerGuard = {
        condTs: guard ? `${guard.condTs} && ${tsExpr} !== null` : `${tsExpr} !== null`,
        condLaw: guard ? `${guard.condLaw} and ${lawExpr} != null` : `${lawExpr} != null`,
      }
      registerKind(reg, rawName, kind.of, tsExpr, lawExpr, innerGuard)
      return
    }
    case 'record':
      for (const [f, fk] of kind.fields) {
        registerKind(reg, `${rawName}.${f}`, fk, propAccess(tsExpr, f), `${lawExpr}.${f}`, guard)
      }
      return
    case 'variant': {
      const names = kind.cases.map(([c]) => c)
      reg.slots.set(rawName, {kind: 'variantTag', ts: wrapTs(tsExpr, kindDefaultTs(kind)), law: wrapLaw(lawExpr), tagKey: kind.tagKey, cases: names})
      for (const [c, fs] of kind.cases) {
        const caseGuard = {
          condTs: guard ? `${guard.condTs} && ${propAccess(tsExpr, kind.tagKey)} === ${JSON.stringify(c)}` : `${propAccess(tsExpr, kind.tagKey)} === ${JSON.stringify(c)}`,
          condLaw: guard ? `${guard.condLaw} and ${lawExpr}.${kind.tagKey} == ${JSON.stringify(c)}` : `${lawExpr}.${kind.tagKey} == ${JSON.stringify(c)}`,
        }
        for (const [f, fk] of fs) {
          registerKind(reg, `${rawName}.${c}.${f}`, fk, propAccess(tsExpr, f), `${lawExpr}.${f}`, caseGuard)
        }
      }
      return
    }
    case 'str':
      reg.slots.set(rawName, {kind: 'strId', ts: wrapTs(tsExpr, "''"), law: wrapLaw(lawExpr), patterns: kind.patterns})
      reg.slots.set(`${rawName}$len`, {kind: 'strLen', ts: wrapTs(`${tsExpr}.length`, '0'), law: wrapLaw(`${lawExpr}.length`)})
      kind.patterns.forEach((p, i) => {
        reg.slots.set(`${rawName}$like${i}`, {kind: 'strLike', ts: wrapTs(tsExpr, "''"), law: wrapLaw(lawExpr), pattern: p})
      })
      return
    case 'fixed': {
      const limbs = kind.width === 8 ? 1 : kind.width / 16
      for (let i = 0; i < limbs; i++) {
        reg.slots.set(`${rawName}$${i}`, {kind: 'nat', ts: `${safeVar('$limb_', rawName)}_${i}`, law: `${lawExpr}$${i}`})
      }
      return
    }
  }
}

// --- Expression & condition emitter (TypeScript runtime code) --------------------------------------------------------

type MapInfo = {
  readonly rawName: string
  readonly mapName: string
  readonly stateExpr: string
  readonly defaultVal: number
  readonly fieldPath?: string[]
  readonly fieldKind?: KindInfo
  readonly dynamicDefaultExpr?: string
}

type EmitCtx = {
  readonly reg: SlotRegistry
  readonly mode: 'rule' | 'standalone'
  readonly flags: Map<string, string>
  readonly maps: Map<string, MapInfo>
  readonly fns: Record<string, Fn>
  readonly helpers: Set<'min' | 'max' | 'sub' | 'glob' | 'cpair' | 'cunpair' | 'dec' | 'idx'>
  readonly fnNames: Map<string, string>
  readonly boundKeys: Map<string, string>
  readonly statePrefix: string
  readonly cse?: Map<string, {ts: string, kind: KindInfo}>
}

function emitTsCode(ctx: EmitCtx) {
  const minCall = (a: string, b: string) => {
    if (ctx.mode === 'standalone') { ctx.helpers.add('min'); return `$min(${a}, ${b})` }
    return `Math.min(${a}, ${b})`
  }
  const maxCall = (a: string, b: string) => {
    if (ctx.mode === 'standalone') { ctx.helpers.add('max'); return `$max(${a}, ${b})` }
    return `Math.max(${a}, ${b})`
  }
  const subCall = (a: string, b: string) => {
    if (ctx.mode === 'standalone') { ctx.helpers.add('sub'); return `$sub(${a}, ${b})` }
    return `Math.max(0, ${a} - ${b})`
  }

  const slotAsNum = (name: string): string => {
    if (ctx.boundKeys.has(name)) return ctx.boundKeys.get(name)!
    const s = ctx.reg.slots.get(name)
    if (!s) return name
    switch (s.kind) {
      case 'nat': case 'strLen': return s.ts
      case 'bool': return `(${s.ts} ? 1 : 0)`
      case 'maybeSome': return `(${s.ts} !== null ? 1 : 0)`
      case 'intPos': return maxCall(s.ts, '0')
      case 'intNeg': return maxCall(`-(${s.ts})`, '0')
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
    if (!info.fieldPath || !info.fieldPath.length) {
      const def = info.dynamicDefaultExpr ?? String(info.defaultVal)
      return {expr: `(${info.stateExpr}.get(${kTs}) ?? ${def})`, kind: info.fieldKind ?? {kind: 'nat'}}
    }
    // Nested record/variant map cell: avoid optional chaining `?.` so TS reader accepts it!
    const getExpr = `${info.stateExpr}.get(${kTs})`
    // Build nested field access: (cell !== undefined ? cell.f : default)
    const fk = info.fieldKind ?? {kind: 'nat'}
    const access = info.fieldPath.reduce((acc, f) => propAccess(acc, f), '$c')
    const def = kindDefaultTs(fk)
    // Inline IIFE? Wait: extract-read.ts refuses arrow functions! Use ternary with repeated .get(k) or helper!
    // Check: state.Acct.get(k) !== undefined ? state.Acct.get(k)!.spent : 0
    // Wait: does extract-read.ts accept `non-null assertion` (`!`) and `map.get(k) !== undefined ? map.get(k)!.spent : 0`?
    // Even better: `(state.Acct.get(k) ?? { limit: 0, spent: 0, frozen: false }).spent` — ZERO `!`, ZERO `?.`, ZERO arrow fn!
    // Wait: what if `info.fieldPath` is for a record cell? Let's pass `cellDefaultTs` on `MapInfo`!
    void access; void def
    return {expr: `(${getExpr} ?? ${info.dynamicDefaultExpr ?? '0'})`, kind: fk}
  }

  const emitFnCall = (map: string, key: E): string | undefined => {
    const mDiv = /^(div|mod)\$(\d+)$/.exec(map)
    if (mDiv) {
      const k = Number(mDiv[2])
      const a = emitNum(key)
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
    switch (e.op) {
      case 'const': return String(e.value)
      case 'var': return slotAsNum(e.name)
      case 'add': {
        const lin = emptyLin()
        addLin(lin, e, 1, ctx.reg.signedVars)
        cancelSigned(lin, ctx.reg.signedVars)
        return formatLin(lin)
      }
      case 'sub': return subCall(emitNum(e.a), emitNum(e.b))
      case 'mul': {
        if (e.k === 0) return '0'
        if (e.k === 1) return emitNum(e.a)
        return `(${e.k} * ${emitNum(e.a)})`
      }
      case 'prod': return `(${emitNum(e.a)} * ${emitNum(e.b)})`
      case 'min': return minCall(emitNum(e.a), emitNum(e.b))
      case 'max': return maxCall(emitNum(e.a), emitNum(e.b))
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
    const pos: string[] = []
    const neg: string[] = []
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
    if (a.op === 'sub' && b.op === 'sub' && sameNode(a.a, b.b) && sameNode(a.b, b.a)) {
      return emitSignedDiff(a.a, a.b)
    }
    if (a.op === 'if' && b.op === 'if' && sameNode(a.c, b.c)) {
      return `(${emitCond(a.c)} ? ${emitSignedDiff(a.then, b.then)} : ${emitSignedDiff(a.else, b.else)})`
    }
    const lin = emptyLin()
    addLin(lin, a, 1, ctx.reg.signedVars)
    addLin(lin, b, -1, ctx.reg.signedVars)
    cancelSigned(lin, ctx.reg.signedVars)
    return formatLin(lin)
  }

  const choiceSlotOf = (e: E): {ts: string, values: readonly string[], tagKey?: string} | undefined => {
    if (ctx.cse?.size) {
      const hit = ctx.cse.get(JSON.stringify(e))
      if (hit?.kind.kind === 'oneOf') return {ts: hit.ts, values: hit.kind.values}
    }
    if (e.op === 'var') {
      const s = ctx.reg.slots.get(e.name)
      if (s?.kind === 'oneOf') return {ts: s.ts, values: s.values}
      if (s?.kind === 'variantTag') return {ts: propAccess(s.ts, s.tagKey), values: s.cases, tagKey: s.tagKey}
    }
    if (e.op === 'get' && ctx.maps.has(e.map)) {
      const info = ctx.maps.get(e.map)!
      if (info.fieldKind?.kind === 'oneOf') return {ts: mapReadExpr(e.map, e.key).expr, values: info.fieldKind.values}
      if (info.fieldKind?.kind === 'variant') {
        return {ts: propAccess(mapReadExpr(e.map, e.key).expr, info.fieldKind.tagKey), values: info.fieldKind.cases.map(([c]) => c)}
      }
    }
    return undefined
  }

  const boolSlotOf = (e: E): string | undefined => {
    if (ctx.cse?.size) {
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
    // Constant fold
    if (a.op === 'const' && b.op === 'const') {
      const res = op === '<' ? a.value < b.value : op === '<=' ? a.value <= b.value : a.value === b.value
      return String(negated ? !res : res)
    }
    // Boolean equality
    if (op === '=') {
      const ba = boolSlotOf(a), bb = boolSlotOf(b)
      if (ba && b.op === 'const' && (b.value === 0 || b.value === 1)) {
        const want = (b.value === 1) !== negated
        return want ? ba : `!(${ba})`
      }
      if (bb && a.op === 'const' && (a.value === 0 || a.value === 1)) {
        const want = (a.value === 1) !== negated
        return want ? bb : `!(${bb})`
      }
      if (ba && bb) return negated ? `(${ba} !== ${bb})` : `(${ba} === ${bb})`
      // Choice / variant tag equality
      const ca = choiceSlotOf(a), cb = choiceSlotOf(b)
      if (ca && b.op === 'const' && b.value >= 0 && b.value < ca.values.length) {
        return `(${ca.ts} ${negated ? '!==' : '==='} ${JSON.stringify(ca.values[b.value]!)})`
      }
      if (cb && a.op === 'const' && a.value >= 0 && a.value < cb.values.length) {
        return `(${cb.ts} ${negated ? '!==' : '==='} ${JSON.stringify(cb.values[a.value]!)})`
      }
      if (ca && cb && ca.values.join('\0') === cb.values.join('\0')) {
        return `(${ca.ts} ${negated ? '!==' : '==='} ${cb.ts})`
      }
      // String id equality
      if (a.op === 'var' && ctx.reg.slots.get(a.name)?.kind === 'strId') {
        const sA = ctx.reg.slots.get(a.name)!
        if (b.op === 'const' && ctx.reg.strLiterals.has(b.value)) {
          return `(${sA.ts} ${negated ? '!==' : '==='} ${JSON.stringify(ctx.reg.strLiterals.get(b.value)!)})`
        }
        if (b.op === 'var' && ctx.reg.slots.get(b.name)?.kind === 'strId') {
          return `(${sA.ts} ${negated ? '!==' : '==='} ${ctx.reg.slots.get(b.name)!.ts})`
        }
      }
    }
    // Boolean range comparisons (0/1 encoding: bool <= 1 -> true, bool < 2 -> true, etc.)
    const baRange = boolSlotOf(a), bbRange = boolSlotOf(b)
    if (baRange && b.op === 'const') {
      const vals = [0, 1].filter(i => { const ok = op === '<' ? i < b.value : op === '<=' ? i <= b.value : i === b.value; return negated ? !ok : ok })
      if (vals.length === 0) return 'false'
      if (vals.length === 2) return 'true'
      return vals[0] === 1 ? baRange : `!(${baRange})`
    }
    if (bbRange && a.op === 'const') {
      const vals = [0, 1].filter(i => { const ok = op === '<' ? a.value < i : op === '<=' ? a.value <= i : a.value === i; return negated ? !ok : ok })
      if (vals.length === 0) return 'false'
      if (vals.length === 2) return 'true'
      return vals[0] === 1 ? bbRange : `!(${bbRange})`
    }
    // Choice range comparisons (e.g., Chart's `among` range checks `state <= 2`)
    const ca = choiceSlotOf(a), cb = choiceSlotOf(b)
    if (ca && b.op === 'const') {
      const keep = ca.values.filter((_, i) => {
        const ok = op === '<' ? i < b.value : op === '<=' ? i <= b.value : i === b.value
        return negated ? !ok : ok
      })
      if (keep.length === 0) return 'false'
      if (keep.length === ca.values.length) return 'true'
      return `(${keep.map(v => `${ca.ts} === ${JSON.stringify(v)}`).join(' || ')})`
    }
    if (cb && a.op === 'const') {
      const keep = cb.values.filter((_, i) => {
        const ok = op === '<' ? a.value < i : op === '<=' ? a.value <= i : a.value === i
        return negated ? !ok : ok
      })
      if (keep.length === 0) return 'false'
      if (keep.length === cb.values.length) return 'true'
      return `(${keep.map(v => `${cb.ts} === ${JSON.stringify(v)}`).join(' || ')})`
    }
    // Linear cancellation for signed Int/Decimal comparisons
    const lin = emptyLin()
    addLin(lin, a, 1, ctx.reg.signedVars)
    addLin(lin, b, -1, ctx.reg.signedVars)
    cancelSigned(lin, ctx.reg.signedVars)
    // Partition into LHS (positive coeff) and RHS (negative coeff)
    const lhs = emptyLin(), rhs = emptyLin()
    for (const [k, c] of lin.signed) { if (c > 0) lhs.signed.set(k, c); else rhs.signed.set(k, -c) }
    for (const [k, c] of lin.vars) { if (c > 0) lhs.vars.set(k, c); else rhs.vars.set(k, -c) }
    for (const r of lin.rest) { if (r.coeff > 0) lhs.rest.push(r); else rhs.rest.push({coeff: -r.coeff, e: r.e}) }
    // Place constant on RHS when LHS has terms, else on LHS
    const lhsHasTerms = lhs.signed.size + lhs.vars.size + lhs.rest.length > 0
    const rhsHasTerms = rhs.signed.size + rhs.vars.size + rhs.rest.length > 0
    if (lhsHasTerms && !rhsHasTerms) rhs.constVal = -lin.constVal
    else if (!lhsHasTerms && rhsHasTerms) lhs.constVal = lin.constVal
    else if (lin.constVal >= 0) lhs.constVal = lin.constVal
    else rhs.constVal = -lin.constVal
    const effOp = !negated
      ? (op === '=' ? '===' : op)
      : (op === '<' ? '>=' : op === '<=' ? '>' : '!==')
    return `(${formatLin(lhs)} ${effOp} ${formatLin(rhs)})`
  }

  const emitCond = (c: C): string => {
    switch (c.op) {
      case '<': case '<=': case '=': return emitCmp(c.op, c.a, c.b, false)
      case 'not': {
        if (c.x.op === 'not') return emitCond(c.x.x)
        if (c.x.op === '<' || c.x.op === '<=' || c.x.op === '=') return emitCmp(c.x.op, c.x.a, c.x.b, true)
        const inner = emitCond(c.x)
        if (inner === 'true') return 'false'
        if (inner === 'false') return 'true'
        return `!(${inner})`
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
      case 'all': throw new Error('emit: quantified condition in runtime code requires expansion')
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
      // Fallback: dispatch on tag index
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

// --- // gdp: law comment printer (matches core/laws.ts grammar) ------------------------------------------------------

type LawPrintCtx = {
  readonly reg: SlotRegistry
  readonly flags: Record<string, C>
  readonly mapReads: Map<string, {mapName: string, field?: string, kind: KindInfo}>
  readonly fns: Record<string, Fn>
  readonly step: boolean
  readonly boundKeys: Set<string>
}

type LawPrintResult = {ok: true, expr: string} | {ok: false, reason: string}

function printLawCondition(c: C, ctx: LawPrintCtx, forallKey?: string): LawPrintResult {
  const fail = (reason: string): LawPrintResult => ({ok: false, reason})
  const mapsAtKey = new Set<string>()
  const primedMapsAtKey = new Set<string>()
  // Alpha-rename internal binder names (e.g., `key$2`) to a clean deterministic identifier accepted by core/laws.ts.
  const keyRename = new Map<string, string>()
  if (forallKey) {
    const used = new Set<string>([...ctx.reg.slots.keys(), ...[...ctx.mapReads.values()].map(m => m.mapName)])
    let clean = 'k'
    for (let n = 1; used.has(clean); n++) clean = `k${n}`
    keyRename.set(forallKey, clean)
  }
  const boundName = (name: string) => keyRename.get(name) ?? name

  const findIfInE = (e: E): {c: C, replace: (sub: E) => E} | undefined => {
    switch (e.op) {
      case 'if': return {c: e.c, replace: sub => sub}
      case 'add': case 'sub': case 'min': case 'max': case 'prod': {
        const l = findIfInE(e.a); if (l) return {c: l.c, replace: sub => ({...e, a: l.replace(sub)})}
        const r = findIfInE(e.b); if (r) return {c: r.c, replace: sub => ({...e, b: r.replace(sub)})}
        return undefined
      }
      case 'mul': { const l = findIfInE(e.a); return l ? {c: l.c, replace: sub => ({op: 'mul', k: e.k, a: l.replace(sub)})} : undefined }
      case 'get': { const l = findIfInE(e.key); return l ? {c: l.c, replace: sub => ({op: 'get', map: e.map, key: l.replace(sub)})} : undefined }
      default: return undefined
    }
  }

  const slotLaw = (name: string): string | undefined => {
    if (ctx.boundKeys.has(name)) return name
    const s = ctx.reg.slots.get(name)
    if (s) return s.law
    return undefined
  }

  const choiceOf = (e: E): {law: string, values: readonly string[]} | undefined => {
    if (e.op === 'var') {
      const s = ctx.reg.slots.get(e.name)
      if (s?.kind === 'oneOf') return {law: s.law, values: s.values}
    }
    if (e.op === 'get') {
      const baseMap = e.map.endsWith("'") ? e.map.slice(0, -1) : e.map
      const m = ctx.mapReads.get(baseMap)
      if (m?.kind.kind === 'oneOf') {
        const k = printE(e.key)
        if (!k.ok) return undefined
        const primed = e.map.endsWith("'")
        const expr = m.field ? `${m.mapName}[${k.expr}].${m.field}` : `${m.mapName}[${k.expr}]`
        return {law: ctx.step && !primed ? `old(${expr})` : expr, values: m.kind.values}
      }
    }
    return undefined
  }

  const boolOf = (e: E): string | undefined => {
    if (e.op === 'var') {
      const s = ctx.reg.slots.get(e.name)
      if (s?.kind === 'bool') return s.law
    }
    if (e.op === 'get') {
      const baseMap = e.map.endsWith("'") ? e.map.slice(0, -1) : e.map
      const m = ctx.mapReads.get(baseMap)
      if (m?.kind.kind === 'bool') {
        const k = printE(e.key)
        if (!k.ok) return undefined
        const primed = e.map.endsWith("'")
        const expr = m.field ? `${m.mapName}[${k.expr}].${m.field}` : `${m.mapName}[${k.expr}]`
        return ctx.step && !primed ? `old(${expr})` : expr
      }
    }
    return undefined
  }

  const printE = (e: E): LawPrintResult => {
    switch (e.op) {
      case 'const': return {ok: true, expr: String(e.value)}
      case 'var': {
        if (ctx.boundKeys.has(e.name)) return {ok: true, expr: boundName(e.name)}
        const s = ctx.reg.slots.get(e.name)
        if (!s) return fail(`unknown law variable ${e.name}`)
        if (s.kind === 'nat') return {ok: true, expr: s.law}
        if (s.kind === 'intPos') return {ok: true, expr: `max(0, ${s.law})`}
        if (s.kind === 'intNeg') return {ok: true, expr: `max(0, -${s.law})`}
        return fail(`non-numeric variable ${e.name} (${s.kind}) in arithmetic position`)
      }
      case 'add': {
        const lin = emptyLin()
        addLin(lin, e, 1, ctx.reg.signedVars)
        cancelSigned(lin, ctx.reg.signedVars)
        return formatLawLin(lin)
      }
      case 'sub': {
        const a = printE(e.a), b = printE(e.b)
        if (!a.ok) return a
        if (!b.ok) return b
        return {ok: true, expr: `max(0, ${a.expr} - ${b.expr})`}
      }
      case 'mul': {
        const a = printE(e.a)
        if (!a.ok) return a
        if (e.k === 0) return {ok: true, expr: '0'}
        if (e.k === 1) return a
        return {ok: true, expr: `(${e.k} * ${a.expr})`}
      }
      case 'prod': return fail('nonlinear product in law is outside TS reader linear grammar')
      case 'min': case 'max': {
        const a = printE(e.a), b = printE(e.b)
        if (!a.ok) return a
        if (!b.ok) return b
        return {ok: true, expr: `${e.op}(${a.expr}, ${b.expr})`}
      }
      case 'if': return fail('un-lifted conditional expression in law')
      case 'tup': case 'proj': return fail('tuple key in law is outside TS reader grammar')
      case 'get': {
        const mDiv = /^(div|mod)\$(\d+)$/.exec(e.map)
        if (mDiv) {
          const a = printE(e.key)
          if (!a.ok) return a
          return {ok: true, expr: mDiv[1] === 'div' ? `(${a.expr} // ${mDiv[2]!})` : `(${a.expr} % ${mDiv[2]!})`}
        }
        const fn = ctx.fns[e.map]
        if (fn) {
          const d = directOf(fn)
          if (d?.kind === 'div' || d?.kind === 'mod') {
            const a = printE(e.key)
            if (!a.ok) return a
            return {ok: true, expr: d.kind === 'div' ? `(${a.expr} // ${d.divisor})` : `(${a.expr} % ${d.divisor})`}
          }
          return fail(`function call ${e.map}(...) is outside TS reader law grammar`)
        }
        const primed = e.map.endsWith("'")
        const baseMap = primed ? e.map.slice(0, -1) : e.map
        const m = ctx.mapReads.get(baseMap)
        if (!m) return fail(`unknown map ${e.map} in law`)
        const k = printE(e.key)
        if (!k.ok) return k
        if (forallKey && e.key.op === 'var' && e.key.name === forallKey) {
          if (primed) primedMapsAtKey.add(m.mapName)
          else mapsAtKey.add(m.mapName)
        }
        const acc = m.field ? `${m.mapName}[${k.expr}].${m.field}` : `${m.mapName}[${k.expr}]`
        return {ok: true, expr: ctx.step && !primed ? `old(${acc})` : acc}
      }
    }
  }

  const formatLawLin = (lin: LinForm): LawPrintResult => {
    const pos: string[] = [], neg: string[] = []
    const push = (expr: string, c: number) => {
      if (c === 1) pos.push(expr)
      else if (c === -1) neg.push(expr)
      else if (c > 1) pos.push(`${c} * ${expr}`)
      else if (c < -1) neg.push(`${-c} * ${expr}`)
    }
    for (const [k, c] of lin.signed) push(ctx.reg.signedLaw.get(k)!, c)
    for (const [k, c] of lin.vars) {
      const s = printE({op: 'var', name: k})
      if (!s.ok) return s
      push(s.expr, c)
    }
    for (const r of lin.rest) {
      const s = printE(r.e)
      if (!s.ok) return s
      push(s.expr, r.coeff)
    }
    if (lin.constVal > 0) pos.push(String(lin.constVal))
    else if (lin.constVal < 0) neg.push(String(-lin.constVal))
    if (!pos.length && !neg.length) return {ok: true, expr: '0'}
    if (!neg.length) return {ok: true, expr: pos.length === 1 ? pos[0]! : `(${pos.join(' + ')})`}
    if (!pos.length) return {ok: true, expr: neg.length === 1 ? `(-${neg[0]!})` : `(-(${neg.join(' + ')}))`}
    return {ok: true, expr: `(${pos.join(' + ')} - ${neg.join(' - ')})`}
  }

  const printCmp = (op: '<' | '<=' | '=', a: E, b: E, negated = false): LawPrintResult => {
    // Lift any `if` inside comparisons into logical implications (core/laws.ts has no ternary `?:`)
    const ifA = findIfInE(a)
    if (ifA) {
      const condRes = printC(ifA.c)
      if (!condRes.ok) return condRes
      const tRes = printCmp(op, ifA.replace((ifA.c ? (a as E) : a) && (() => {
        const sub = (x: E): E => x === a ? ifA.replace(findIfNode(a)!.then) : x
        return sub(a)
      })()), b, negated)
      const eRes = printCmp(op, ifA.replace(findIfNode(a)!.else), b, negated)
      if (!tRes.ok) return tRes
      if (!eRes.ok) return eRes
      return {ok: true, expr: `((${condRes.expr} implies ${tRes.expr}) and ((not (${condRes.expr})) implies ${eRes.expr}))`}
    }
    const ifB = findIfInE(b)
    if (ifB) {
      const condRes = printC(ifB.c)
      if (!condRes.ok) return condRes
      const tRes = printCmp(op, a, ifB.replace(findIfNode(b)!.then), negated)
      const eRes = printCmp(op, a, ifB.replace(findIfNode(b)!.else), negated)
      if (!tRes.ok) return tRes
      if (!eRes.ok) return eRes
      return {ok: true, expr: `((${condRes.expr} implies ${tRes.expr}) and ((not (${condRes.expr})) implies ${eRes.expr}))`}
    }
    if (a.op === 'const' && b.op === 'const') {
      const res = op === '<' ? a.value < b.value : op === '<=' ? a.value <= b.value : a.value === b.value
      return {ok: true, expr: String(negated ? !res : res)}
    }
    if (op === '=') {
      const ba = boolOf(a), bb = boolOf(b)
      if (ba && b.op === 'const' && (b.value === 0 || b.value === 1)) {
        const want = (b.value === 1) !== negated
        return {ok: true, expr: want ? ba : `(not ${ba})`}
      }
      if (bb && a.op === 'const' && (a.value === 0 || a.value === 1)) {
        const want = (a.value === 1) !== negated
        return {ok: true, expr: want ? bb : `(not ${bb})`}
      }
      if (ba && bb) return {ok: true, expr: `(${ba} ${negated ? '!=' : '=='} ${bb})`}
      const ca = choiceOf(a), cb = choiceOf(b)
      if (ca && b.op === 'const' && b.value >= 0 && b.value < ca.values.length) {
        return {ok: true, expr: `(${ca.law} ${negated ? '!=' : '=='} ${JSON.stringify(ca.values[b.value]!)})`}
      }
      if (cb && a.op === 'const' && a.value >= 0 && a.value < cb.values.length) {
        return {ok: true, expr: `(${cb.law} ${negated ? '!=' : '=='} ${JSON.stringify(cb.values[a.value]!)})`}
      }
      if (ca && cb && ca.values.join('\0') === cb.values.join('\0')) {
        return {ok: true, expr: `(${ca.law} ${negated ? '!=' : '=='} ${cb.law})`}
      }
    }
    const baR = boolOf(a), bbR = boolOf(b)
    if (baR && b.op === 'const') {
      const vals = [0, 1].filter(i => { const ok = op === '<' ? i < b.value : op === '<=' ? i <= b.value : i === b.value; return negated ? !ok : ok })
      if (vals.length === 0) return {ok: true, expr: 'false'}
      if (vals.length === 2) return {ok: true, expr: 'true'}
      return {ok: true, expr: vals[0] === 1 ? baR : `(not ${baR})`}
    }
    if (bbR && a.op === 'const') {
      const vals = [0, 1].filter(i => { const ok = op === '<' ? a.value < i : op === '<=' ? a.value <= i : a.value === i; return negated ? !ok : ok })
      if (vals.length === 0) return {ok: true, expr: 'false'}
      if (vals.length === 2) return {ok: true, expr: 'true'}
      return {ok: true, expr: vals[0] === 1 ? bbR : `(not ${bbR})`}
    }
    const ca = choiceOf(a), cb = choiceOf(b)
    if (ca && b.op === 'const') {
      const keep = ca.values.filter((_, i) => {
        const ok = op === '<' ? i < b.value : op === '<=' ? i <= b.value : i === b.value
        return negated ? !ok : ok
      })
      if (keep.length === 0) return {ok: true, expr: 'false'}
      if (keep.length === ca.values.length) return {ok: true, expr: 'true'}
      return {ok: true, expr: `(${keep.map(v => `${ca.law} == ${JSON.stringify(v)}`).join(' or ')})`}
    }
    if (cb && a.op === 'const') {
      const keep = cb.values.filter((_, i) => {
        const ok = op === '<' ? a.value < i : op === '<=' ? a.value <= i : a.value === i
        return negated ? !ok : ok
      })
      if (keep.length === 0) return {ok: true, expr: 'false'}
      if (keep.length === cb.values.length) return {ok: true, expr: 'true'}
      return {ok: true, expr: `(${keep.map(v => `${cb.law} == ${JSON.stringify(v)}`).join(' or ')})`}
    }
    const lin = emptyLin()
    addLin(lin, a, 1, ctx.reg.signedVars)
    addLin(lin, b, -1, ctx.reg.signedVars)
    cancelSigned(lin, ctx.reg.signedVars)
    const lhs = emptyLin(), rhs = emptyLin()
    for (const [k, coef] of lin.signed) { if (coef > 0) lhs.signed.set(k, coef); else rhs.signed.set(k, -coef) }
    for (const [k, coef] of lin.vars) { if (coef > 0) lhs.vars.set(k, coef); else rhs.vars.set(k, -coef) }
    for (const r of lin.rest) { if (r.coeff > 0) lhs.rest.push(r); else rhs.rest.push({coeff: -r.coeff, e: r.e}) }
    const lhsHas = lhs.signed.size + lhs.vars.size + lhs.rest.length > 0
    const rhsHas = rhs.signed.size + rhs.vars.size + rhs.rest.length > 0
    if (lhsHas && !rhsHas) rhs.constVal = -lin.constVal
    else if (!lhsHas && rhsHas) lhs.constVal = lin.constVal
    else if (lin.constVal >= 0) lhs.constVal = lin.constVal
    else rhs.constVal = -lin.constVal
    const lStr = formatLawLin(lhs), rStr = formatLawLin(rhs)
    if (!lStr.ok) return lStr
    if (!rStr.ok) return rStr
    const effOp = !negated
      ? (op === '=' ? '==' : op)
      : (op === '<' ? '>=' : op === '<=' ? '>' : '!=')
    return {ok: true, expr: `(${lStr.expr} ${effOp} ${rStr.expr})`}
  }

  const findIfNode = (e: E): (E & {op: 'if'}) | undefined => {
    switch (e.op) {
      case 'if': return e
      case 'add': case 'sub': case 'min': case 'max': case 'prod': return findIfNode(e.a) ?? findIfNode(e.b)
      case 'mul': return findIfNode(e.a)
      case 'get': return findIfNode(e.key)
      default: return undefined
    }
  }

  const printC = (cond: C): LawPrintResult => {
    switch (cond.op) {
      case '<': case '<=': case '=': return printCmp(cond.op, cond.a, cond.b, false)
      case 'not': {
        if (cond.x.op === 'not') return printC(cond.x.x)
        if (cond.x.op === '<' || cond.x.op === '<=' || cond.x.op === '=') return printCmp(cond.x.op, cond.x.a, cond.x.b, true)
        const inner = printC(cond.x)
        if (!inner.ok) return inner
        if (inner.expr === 'true') return {ok: true, expr: 'false'}
        if (inner.expr === 'false') return {ok: true, expr: 'true'}
        return {ok: true, expr: `(not ${inner.expr})`}
      }
      case 'and': {
        const parts: string[] = []
        for (const x of cond.xs) {
          const r = printC(x)
          if (!r.ok) return r
          if (r.expr === 'false') return {ok: true, expr: 'false'}
          if (r.expr !== 'true' && !parts.includes(r.expr)) parts.push(r.expr)
        }
        return {ok: true, expr: parts.length === 0 ? 'true' : parts.length === 1 ? parts[0]! : `(${parts.join(' and ')})`}
      }
      case 'or': {
        // Detect implication: (not A) or B -> A implies B
        if (cond.xs.length === 2 && cond.xs[0]!.op === 'not') {
          const ant = printC(cond.xs[0]!.x), con = printC(cond.xs[1]!)
          if (!ant.ok) return ant
          if (!con.ok) return con
          if (ant.expr === 'false') return {ok: true, expr: 'true'}
          if (ant.expr === 'true') return con
          return {ok: true, expr: `(${ant.expr} implies ${con.expr})`}
        }
        const parts: string[] = []
        for (const x of cond.xs) {
          const r = printC(x)
          if (!r.ok) return r
          if (r.expr === 'true') return {ok: true, expr: 'true'}
          if (r.expr !== 'false' && !parts.includes(r.expr)) parts.push(r.expr)
        }
        return {ok: true, expr: parts.length === 0 ? 'false' : parts.length === 1 ? parts[0]! : `(${parts.join(' or ')})`}
      }
      case 'flag': {
        const def = ctx.flags[cond.name]
        if (!def) return fail(`unknown flag ${cond.name} in law`)
        return printC(def)
      }
      case 'all': return fail('nested quantifier in law is outside TS reader grammar')
    }
  }

  void slotLaw
  const body = printC(c)
  if (!body.ok) return body
  if (forallKey) {
    const allMaps = [...new Set([...mapsAtKey, ...primedMapsAtKey])]
    if (allMaps.length !== 1) {
      return fail(allMaps.length === 0
        ? `quantified key ${forallKey} does not index a single map`
        : `quantified key ${forallKey} spans multiple maps (${allMaps.join(', ')})`)
    }
    const targetMap = allMaps[0]!
    const domain = ctx.step && mapsAtKey.has(targetMap) && !primedMapsAtKey.has(targetMap) ? `old(${targetMap})` : targetMap
    return {ok: true, expr: `forall ${boundName(forallKey)} in ${domain}: ${stripOuterParens(body.expr)}`}
  }
  return {ok: true, expr: stripOuterParens(body.expr)}
}

function stripOuterParens(s: string): string {
  while (s.startsWith('(') && s.endsWith(')')) {
    let depth = 0, ok = true
    for (let i = 0; i < s.length - 1; i++) {
      if (s[i] === '(') depth++
      else if (s[i] === ')' && --depth === 0) { ok = false; break }
    }
    if (!ok) break
    s = s.slice(1, -1)
  }
  return s
}

// --- Helper functions emitted only when used -------------------------------------------------------------------------

function renderHelpers(helpers: ReadonlySet<string>): string[] {
  const out: string[] = []
  if (helpers.has('min')) out.push('function $min(a: number, b: number): number { return a <= b ? a : b }')
  if (helpers.has('max')) out.push('function $max(a: number, b: number): number { return a >= b ? a : b }')
  if (helpers.has('sub')) out.push('function $sub(a: number, b: number): number { return a >= b ? a - b : 0 }')
  if (helpers.has('idx')) out.push('function $idx<T extends string>(v: T, xs: readonly T[]): number { const i = xs.indexOf(v); if (i < 0) throw new RangeError(`unexpected choice ${v}`); return i }')
  if (helpers.has('dec')) {
    out.push(
      'function $dec(x: number, places: number, scale: number, name: string): number {',
      '  if (!Number.isFinite(x)) throw new RangeError(`${name}: expected finite decimal`)',
      '  const text = x.toFixed(places + 3)',
      '  const m = /^(-?)(\\d+)(?:\\.(\\d+))?$/.exec(text)',
      '  if (!m) throw new RangeError(`${name}: invalid decimal ${x}`)',
      "  const frac = (m[3] ?? '').replace(/0+$/, '')",
      '  if (frac.length > places) throw new RangeError(`${name}: exceeds ${places} decimal places`)',
      "  const n = Number(m[2]) * scale + Number(frac.padEnd(places, '0') || '0')",
      '  if (!Number.isSafeInteger(n)) throw new RangeError(`${name}: decimal out of safe integer range`)',
      '  return m[1] && n !== 0 ? -n : n',
      '}',
    )
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
      '  if (!Number.isSafeInteger(v)) throw new RangeError(\'tuple key passed safe integer range\')',
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
  const rawSrc = fn.call ?? fn.js
  return [`const ${fnId} = (${rawSrc}) as (${params}) => number`]
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
        const ufn = d.uses[e.map]!
        const uid = useNames.get(e.map)!
        const arity = ufn.arity ?? 1
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
}): string[] {
  const lines = [
    `// Generated by gdp-wired ${GDP_WIRED_VERSION}`,
    `// ${info.kind === 'fun' ? 'Pure rule' : info.kind === 'ratRule' ? 'Rational rule' : info.kind === 'chart' ? 'Statechart' : 'Rule'}: ${sanitizeComment(info.name)}`,
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

// --- Guard builders for runtime validation ---------------------------------------------------------------------------

function kindGuardChecks(k: KindInfo, expr: string, label: string, readerSafe: boolean): string[] {
  switch (k.kind) {
    case 'nat': {
      const checks = readerSafe
        ? [`!(${expr} >= 0)`]
        : [`(!Number.isSafeInteger(${expr}) || ${expr} < 0)`]
      if (k.max !== undefined) checks.push(readerSafe ? `(${expr} > ${k.max})` : `(${expr} > ${k.max})`)
      return checks
    }
    case 'int':
      return readerSafe ? [] : [`!Number.isSafeInteger(${expr})`]
    case 'oneOf':
      return readerSafe ? [] : [`!(${k.values.map(v => `${expr} === ${JSON.stringify(v)}`).join(' || ')})`]
    case 'maybe': {
      const inner = kindGuardChecks(k.of, expr, label, readerSafe)
      return inner.length ? [`(${expr} !== null && (${inner.join(' || ')}))`] : []
    }
    case 'record':
      return k.fields.flatMap(([f, fk]) => kindGuardChecks(fk, propAccess(expr, f), `${label}.${f}`, readerSafe))
    case 'variant':
      return k.cases.flatMap(([c, fs]) => {
        const inner = fs.flatMap(([f, fk]) => kindGuardChecks(fk, propAccess(expr, f), `${label}.${c}.${f}`, readerSafe))
        return inner.length ? [`(${propAccess(expr, k.tagKey)} === ${JSON.stringify(c)} && (${inner.join(' || ')}))`] : []
      })
    case 'str':
      return k.maxLength !== undefined ? [`(${expr}.length > ${k.maxLength})`] : []
    default:
      return []
  }
}

// --- emitFun ---------------------------------------------------------------------------------------------------------

export function emitFun(f: Fun<object, object, object>, opts: EmitFunOptions = {}): EmitResult {
  const meta = inspectFunMeta(f)
  const laws = opts.laws ? [...opts.laws] : meta.ownedLaws
  const reports: EmitLawReport[] = []
  let allProven = laws.length > 0
  let firstFailed: Verdict | undefined
  for (const d of laws) {
    if (funOf(d) !== f) {
      allProven = false
      reports.push({name: d.name, kind: 'decision', proven: false, checked: false, why: `law was not stated on function ${meta.name}`})
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
  const hasDecimals = meta.params.some(([, , k]) => hasDecimalKind(k))
    || meta.inputs.some(([, , k]) => hasDecimalKind(k))
    || meta.outputs.some(([, , k]) => hasDecimalKind(k))

  // Check if in standalone TS reader subset
  const verifyReasons: string[] = []
  if (meta.params.some(([, , k]) => !isStandaloneKind(k))) verifyReasons.push('params include compound or string/maybe kinds outside standalone subset')
  if (meta.inputs.some(([, , k]) => !isStandaloneKind(k))) verifyReasons.push('inputs include compound or string/maybe kinds outside standalone subset')
  if (meta.outputs.some(([, , k]) => !isStandaloneKind(k))) verifyReasons.push('result includes compound or string/maybe kinds outside standalone subset')
  if (m.fns && Object.keys(m.fns).some(n => !/^(div|mod)\$\d+$/.test(n))) verifyReasons.push('function calls outside div/mod are not in standalone subset')
  if (m.inputMaps?.length || m.counts || m.leasts || m.history) verifyReasons.push('maps, counts, or history are outside standalone subset')
  if (meta.inputs.some(([n]) => !PLAIN_IDENT.test(n)) || meta.params.some(([n]) => !PLAIN_IDENT.test(n)) || meta.outputs.some(([n]) => !PLAIN_IDENT.test(n))) {
    verifyReasons.push('non-identifier field names are outside standalone subset')
  }

  const reg = makeRegistry()
  for (const [n, , k] of meta.params) registerKind(reg, n, k, propAccess('params', n), `params.${n}`)
  for (const [n, , k] of meta.inputs) registerKind(reg, n, k, propAccess('args', n), `args.${n}`)
  for (const [n, , k] of meta.outputs) registerKind(reg, `$out.${n}`, k, propAccess('result', n), `result.${n}`)

  // Build law comments using symbolic Fun.law callbacks (so laws reference `result.<field>`, never tautologically inlined)
  const lawComments: {name: string, expr: string}[] = []
  const lawAntecedents: C[] = []
  for (const [n, , k] of meta.params) {
    if (k.kind === 'nat') {
      lawAntecedents.push({op: '<=', a: {op: 'const', value: 0}, b: {op: 'var', name: n}})
      if (k.max !== undefined) lawAntecedents.push({op: '<=', a: {op: 'var', name: n}, b: {op: 'const', value: k.max}})
    }
  }
  for (const [n, , k] of meta.inputs) {
    if (k.kind === 'nat') {
      lawAntecedents.push({op: '<=', a: {op: 'const', value: 0}, b: {op: 'var', name: n}})
      if (k.max !== undefined) lawAntecedents.push({op: '<=', a: {op: 'var', name: n}, b: {op: 'const', value: k.max}})
    }
  }
  if (m.pre) lawAntecedents.push(m.pre)
  if (m.assume) lawAntecedents.push(m.assume)

  if (verifyReasons.length === 0) {
    const lctx: LawPrintCtx = {reg, flags: m.step.flags ?? {}, mapReads: new Map(), fns: m.fns ?? {}, step: false, boundKeys: new Set()}
    for (let i = 0; i < laws.length; i++) {
      const d = laws[i]!
      const sym = funSymbolicLaw(f, d)
      if (!sym) { verifyReasons.push(`law "${d.name}" has no symbolic Fun callback`); continue }
      if (sym.kind === 'relate') { verifyReasons.push(`relational 2-call law "${d.name}" is outside standalone single-call reader`); continue }
      const full: C = {
        op: 'or',
        xs: [{op: 'not', x: {op: 'and', xs: [...lawAntecedents, ...sym.given]}}, sym.then],
      }
      const printed = printLawCondition(full, lctx)
      if (!printed.ok) { verifyReasons.push(`law "${d.name}": ${printed.reason}`); continue }
      lawComments.push({name: d.name, expr: printed.expr})
      reports[i] = {...reports[i]!, lawExpr: printed.expr}
    }
  }

  const verifiable = verifyReasons.length === 0 && lawComments.length === laws.length && laws.length > 0
  // Determine whether we need a separate wrapper around a pure core function:
  // standalone mode refuses `throw`, default params, float literals, and `Number.*`.
  const inputChecks = meta.inputs.flatMap(([n, , k]) => kindGuardChecks(k, propAccess('args', n), n, false))
  const paramChecks = meta.params.flatMap(([n, , k]) => kindGuardChecks(k, propAccess('params', n), n, false))
  const needsWrapper = hasDecimals || !!opts.defaultParams || inputChecks.length > 0 || paramChecks.length > 0 || !!m.pre || !!m.assume
  const coreName = verifiable && needsWrapper ? (hasDecimals ? `${fnName}Scaled` : `${fnName}Core`) : fnName

  // Collect custom fns (if any)
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

  const ctx: EmitCtx = {
    reg,
    mode: verifiable ? 'standalone' : 'rule',
    flags: new Map(),
    maps: new Map(),
    fns: m.fns ?? {},
    helpers: new Set(),
    fnNames,
    boundKeys: new Map(),
    statePrefix: 'state',
    cse: new Map(),
  }
  const em = emitTsCode(ctx)

  // Emit core function body
  const flagLines: string[] = []
  for (const [fname, fc] of Object.entries(m.step.flags ?? {})) {
    const local = safeVar('$flag_', fname)
    flagLines.push(`  const ${local}: boolean = ${em.emitCond(fc)}`)
    ctx.flags.set(fname, local)
  }
  const outLocals: string[] = []
  const outExprs: [string, string][] = []
  for (const [n, , k] of meta.outputs) {
    const val = em.emitKindVal(k, `out.${n}`, part => m.step.state?.[part] ?? m.state[part] ?? {op: 'const', value: 0})
    if (meta.outputs.length > 1) {
      const local = PLAIN_IDENT.test(n) && !RESERVED_IDENT.has(n) && n !== 'args' && n !== 'params' ? n : safeVar('$out_', n)
      outLocals.push(`  const ${local}: ${kindTsType(k)} = ${val}`)
      if (k.kind === 'oneOf' || k.kind === 'bool' || k.kind === 'nat') {
        const rawE = m.step.state?.[`out.${n}`]
        if (rawE) ctx.cse!.set(JSON.stringify(rawE), {ts: local, kind: k})
      }
      outExprs.push([n, local])
    } else {
      outExprs.push([n, val])
    }
  }
  // If any output is a decimal, public wrapper converts scaled integer back by `/ 10**places`
  if (hasDecimals) ctx.helpers.add('dec')

  const decPlaces = [...meta.params, ...meta.inputs, ...meta.outputs]
    .flatMap(([, , k]) => (k.kind === 'decimal' ? [k.places] : []))
  const arithDesc = hasDecimals
    ? `exact scaled fixed-point integers (${[...new Set(decPlaces)].sort((a, b) => a - b).map(p => `10^-${p}`).join(', ')}); safe integer range <= 2^53 - 1`
    : 'exact JavaScript safe integers over Z/N (truncated natural subtraction max(0, a - b); safe range <= 2^53 - 1)'

  const lines: string[] = [
    ...renderHeader({name: meta.name, kind: 'fun', digest, arithmetic: arithDesc, laws: reports}),
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

  // Pure helpers needed by core (excluding `$dec` which is only used by wrapper)
  const coreHelpers = new Set([...ctx.helpers].filter(h => h !== 'dec'))
  const coreHelperLines = renderHelpers(coreHelpers)
  if (coreHelperLines.length) lines.push(...coreHelperLines, '')
  if (fnHelperLines.length) lines.push(...fnHelperLines, '')

  // Emit core function (with // gdp: law comments if verifiable)
  if (verifiable) {
    for (const l of lawComments) lines.push(`// gdp: law ${sanitizeComment(l.name)}: ${l.expr}`)
  }
  const coreSig = hasParams ? `(args: Input, params: Params): Result` : `(args: Input): Result`
  lines.push(`export function ${coreName}${coreSig} {`)
  if (!verifiable && !needsWrapper) {
    // Non-verifiable direct function: keep body clean
  }
  lines.push(...flagLines)
  lines.push(...outLocals)
  if (outExprs.length === 1) {
    lines.push(`  return { ${propKey(outExprs[0]![0])}: ${outExprs[0]![1]} }`)
  } else {
    lines.push('  return {')
    for (const [n, expr] of outExprs) {
      lines.push(`    ${propKey(n)}: ${expr},`)
    }
    lines.push('  }')
  }
  lines.push('}')

  // If wrapper needed (decimals, validation, defaultParams, pre/assume)
  if (needsWrapper && coreName !== fnName) {
    if (ctx.helpers.has('dec')) lines.push('', ...renderHelpers(new Set(['dec'])))
    if (hasParams && opts.defaultParams) {
      lines.push('', 'export function defaultParams(): Params {', '  return {')
      for (const [n] of meta.params) {
        const val = opts.defaultParams[n]
        lines.push(`    ${propKey(n)}: ${JSON.stringify(val)},`)
      }
      lines.push('  }', '}')
    }
    const pubSig = hasParams
      ? (opts.defaultParams ? '(args: Input, params: Params = defaultParams()): Result' : '(args: Input, params: Params): Result')
      : '(args: Input): Result'
    lines.push('', `export function ${fnName}${pubSig} {`)
    // Validate & scale params
    if (hasParams) {
      if (hasDecimals) {
        lines.push('  const $p: Params = {')
        for (const [n, , k] of meta.params) {
          const acc = propAccess('params', n)
          if (k.kind === 'decimal') lines.push(`    ${propKey(n)}: $dec(${acc}, ${k.places}, ${10 ** k.places}, ${JSON.stringify(n)}),`)
          else lines.push(`    ${propKey(n)}: ${acc},`)
        }
        lines.push('  }')
      }
      for (const chk of paramChecks) lines.push(`  if (${chk}) throw new RangeError(${JSON.stringify(`${meta.name}: invalid params`)})`)
    }
    if (hasDecimals) {
      lines.push('  const $a: Input = {')
      for (const [n, , k] of meta.inputs) {
        const acc = propAccess('args', n)
        if (k.kind === 'decimal') lines.push(`    ${propKey(n)}: $dec(${acc}, ${k.places}, ${10 ** k.places}, ${JSON.stringify(n)}),`)
        else lines.push(`    ${propKey(n)}: ${acc},`)
      }
      lines.push('  }')
    }
    for (const chk of inputChecks) lines.push(`  if (${chk}) throw new RangeError(${JSON.stringify(`${meta.name}: invalid input`)})`)
    // Check pre / assume over scaled values
    if (m.pre || m.assume) {
      const wReg = makeRegistry()
      for (const [n, , k] of meta.params) registerKind(wReg, n, k, propAccess(hasDecimals ? '$p' : 'params', n), n)
      for (const [n, , k] of meta.inputs) registerKind(wReg, n, k, propAccess(hasDecimals ? '$a' : 'args', n), n)
      const wCtx: EmitCtx = {...ctx, reg: wReg, mode: 'rule'}
      const wEm = emitTsCode(wCtx)
      if (m.pre) {
        const preExpr = wEm.emitCond(m.pre)
        if (preExpr !== 'true') lines.push(`  if (!(${preExpr})) throw new RangeError(${JSON.stringify(`${meta.name}: params violate precondition`)})`)
      }
      if (m.assume) {
        const assumeExpr = wEm.emitCond(m.assume)
        if (assumeExpr !== 'true') lines.push(`  if (!(${assumeExpr})) throw new RangeError(${JSON.stringify(`${meta.name}: input violates assumption`)})`)
      }
    }
    const call = hasParams
      ? `${coreName}(${hasDecimals ? '$a' : 'args'}, ${hasDecimals ? '$p' : 'params'})`
      : `${coreName}(${hasDecimals ? '$a' : 'args'})`
    const hasDecimalOut = meta.outputs.some(([, , k]) => hasDecimalKind(k))
    if (hasDecimalOut) {
      lines.push(`  const $r = ${call}`)
      lines.push('  return {')
      for (const [n, , k] of meta.outputs) {
        const acc = propAccess('$r', n)
        if (k.kind === 'decimal') lines.push(`    ${propKey(n)}: ${acc} / ${10 ** k.places},`)
        else lines.push(`    ${propKey(n)}: ${acc},`)
      }
      lines.push('  }')
    } else {
      lines.push(`  return ${call}`)
    }
    lines.push('}')
  } else if (hasParams && opts.defaultParams) {
    // Non-verifiable with defaultParams: export defaultParams() alongside
    lines.push('', 'export function defaultParams(): Params {', '  return {')
    for (const [n] of meta.params) lines.push(`    ${propKey(n)}: ${JSON.stringify(opts.defaultParams[n])},`)
    lines.push('  }', '}')
  }

  lines.push('')
  return {
    source: lines.join('\n'),
    digest,
    version: GDP_WIRED_VERSION,
    name: meta.name,
    kind: 'fun',
    laws: reports,
    allProven,
    verify: {
      verifiable,
      ...(verifiable ? {entry: coreName, mode: 'standalone' as const} : {}),
      expectedLaws: verifiable ? lawComments.map(l => l.name) : [],
      reasons: verifyReasons,
    },
  }
}

// --- emitRule --------------------------------------------------------------------------------------------------------

export function emitRule(r: Rule<object, object, object, object, object, object, object, object>, opts: EmitRuleOptions = {}): EmitResult {
  return emitRuleInternal(r, opts, 'rule')
}

export function emitChart(c: Chart<object, object, object>, opts: EmitChartOptions = {}): EmitResult {
  const {ownedLaws, ownedStepLaws} = inspectChart(c)
  const userLaws = opts.laws ? [...opts.laws] : ownedLaws
  const userSteps = opts.stepLaws ? [...opts.stepLaws] : ownedStepLaws
  const chartBuiltIn = c.chartLaws()
  const laws = [...chartBuiltIn, ...userLaws]
  return emitRuleInternal(c.rule as never, {...opts, laws, stepLaws: userSteps}, 'chart')
}

function emitRuleInternal(
  r: Rule<object, object, object, object, object, object, object, object>,
  opts: EmitRuleOptions,
  kind: 'rule' | 'chart',
): EmitResult {
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
    const v = stepLaws.length > 0 ? proveSteps(r as never, laws, stepLaws, proveOpts) : proveRule(r as never, laws, proveOpts)
    const assumesList = v.assumes?.laws
    const ok = v.proven && v.checked && !(opts.from === 'any' && assumesList?.length)
    if (!ok) {
      allProven = false
      failedVerdict = v
    }
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
  const className = toPascal(opts.name ?? meta.name)
  const hasParams = meta.params.length > 0
  const hasInputs = meta.inputs.length > 0
  const hasDecimals = meta.params.some(([, , k]) => hasDecimalKind(k))
    || meta.inputs.some(([, , k]) => hasDecimalKind(k))
    || meta.state.some(([, k]) => hasDecimalKind(k))
    || meta.maps.some(([, , k]) => !!k && hasDecimalKind(k))

  // Check if in TS reader class-verification subset
  const verifyReasons: string[] = []
  if (meta.hasHistory) verifyReasons.push('history/log queries and pruning are outside the TS reader class subset')
  if (meta.hasCarried) verifyReasons.push('carried maps/lists are outside the TS reader class subset')
  if (meta.hasCounts) verifyReasons.push('counted maps are outside the TS reader class subset')
  if (meta.hasLeasts) verifyReasons.push('least-key queries are outside the TS reader class subset')
  if (meta.hasNodes) verifyReasons.push('node tables are outside the TS reader class subset')
  if (meta.hasRels) verifyReasons.push('tuple relations are outside the TS reader class subset')
  if (meta.hasSums || (m.sums && Object.keys(m.sums).length > 0)) verifyReasons.push('derived map sums are outside the TS reader class subset')
  if (meta.items.length > 0) verifyReasons.push('kinded item lists are outside the TS reader class subset')
  if (hasDecimals) verifyReasons.push('decimal fixed-point scaling in stateful rules is outside the TS reader class subset')
  if (m.primitiveFailure) verifyReasons.push('fixed-width primitive traps are outside the TS reader class subset')
  if (Object.values(m.step.maps ?? {}).some(w => 'each' in w)) verifyReasons.push('per-key broadcast map writes (each) are outside the TS reader class subset')
  if (Object.values(m.step.flags ?? {}).some(c => JSON.stringify(c).includes('"op":"all"'))) verifyReasons.push('quantified flags are outside the TS reader class subset')
  if (m.fns && Object.keys(m.fns).some(n => {
    if (/^(div|mod)\$\d+$/.test(n)) return false
    const d = directOf(m.fns![n]!)
    return !(d?.kind === 'div' || d?.kind === 'mod')
  })) verifyReasons.push('external or recursive helper functions (beyond constant div/mod) are outside the TS reader class subset')
  if (meta.params.some(([n, , k]) => !PLAIN_IDENT.test(n) || !isSimpleReaderKind(k))) verifyReasons.push('params include compound/maybe/str/non-identifier fields outside the TS reader class subset')
  if (meta.inputs.some(([n, , k]) => !PLAIN_IDENT.test(n) || !isSimpleReaderKind(k))) verifyReasons.push('inputs include compound/maybe/str/non-identifier fields outside the TS reader class subset')
  if (meta.state.some(([n, k]) => !PLAIN_IDENT.test(n) || !isSimpleReaderKind(k))) verifyReasons.push('state includes compound/maybe/str/non-identifier fields outside the TS reader class subset')
  if (meta.maps.some(([n, dflt, k]) => {
    if (!PLAIN_IDENT.test(n)) return true
    if (!k) return dflt !== 0
    if (k.kind === 'record') return k.fields.some(([, fk]) => !isSimpleReaderKind(fk))
    return true
  })) verifyReasons.push('maps include non-zero defaults or non-record compound kinds outside the TS reader class subset')
  if (laws.some(l => !!l.some || (l.keys && l.keys.length > 0))) verifyReasons.push('existential or multi-key universal laws are outside the TS reader law grammar')
  if (stepLaws.some(sl => (sl.steps ?? 1) > 1 || (sl.keys && sl.keys.length > 0))) verifyReasons.push('multi-step or multi-key step laws are outside the TS reader law grammar')

  // Build registries for runtime codegen AND law printing
  const reg = makeRegistry()
  for (const [n, , k] of meta.params) registerKind(reg, n, k, propAccess('params', n), n)
  for (const [n, , k] of meta.inputs) registerKind(reg, n, k, propAccess('input', n), `input.${n}`)
  for (const [n, k] of meta.state) registerKind(reg, n, k, propAccess('state', n), n)

  // Step-law registry (unprimed state = old(x), primed state x' = x)
  const stepReg = makeRegistry()
  for (const [n, , k] of meta.params) registerKind(stepReg, n, k, propAccess('params', n), n)
  for (const [n, , k] of meta.inputs) registerKind(stepReg, n, k, propAccess('input', n), `input.${n}`)
  for (const [n, k] of meta.state) {
    registerKind(stepReg, n, k, propAccess('state', n), `old(${n})`)
    registerKind(stepReg, `${n}'`, k, propAccess('state', n), n)
  }

  // Register maps (both plain maps and kinded record/variant maps)
  const mapInfos = new Map<string, MapInfo>()
  const lawMapReads = new Map<string, {mapName: string, field?: string, kind: KindInfo}>()
  const eachMaps = new Set<string>()
  for (const [rawMap, w] of Object.entries(m.step.maps ?? {})) if ('each' in w) eachMaps.add(rawMap)

  for (const [mapName, dflt, cellKind] of meta.maps) {
    if (!cellKind) {
      mapInfos.set(mapName, {
        rawName: mapName,
        mapName,
        stateExpr: propAccess('state', mapName),
        defaultVal: dflt,
        fieldKind: {kind: 'nat'},
        ...(eachMaps.has(mapName) ? {dynamicDefaultExpr: propAccess('state', `${mapName}_default`)} : {}),
      })
      lawMapReads.set(mapName, {mapName, kind: {kind: 'nat'}})
    } else if (cellKind.kind === 'record') {
      const defObj = kindDefaultTs(cellKind)
      for (const [f, fk] of cellKind.fields) {
        const raw = `${mapName}.${f}`
        mapInfos.set(raw, {
          rawName: raw,
          mapName,
          stateExpr: propAccess('state', mapName),
          defaultVal: m.maps?.[raw] ?? 0,
          fieldPath: [f],
          fieldKind: fk,
          dynamicDefaultExpr: defObj,
        })
        lawMapReads.set(raw, {mapName, field: f, kind: fk})
      }
    } else {
      // Variant or scalar kinded map: register tag + case fields
      const defObj = kindDefaultTs(cellKind)
      mapInfos.set(mapName, {
        rawName: mapName,
        mapName,
        stateExpr: propAccess('state', mapName),
        defaultVal: m.maps?.[mapName] ?? 0,
        fieldKind: cellKind,
        dynamicDefaultExpr: defObj,
      })
      if (cellKind.kind === 'variant') {
        for (const [c, fs] of cellKind.cases) {
          for (const [f, fk] of fs) {
            const raw = `${mapName}.${c}.${f}`
            mapInfos.set(raw, {
              rawName: raw,
              mapName,
              stateExpr: propAccess('state', mapName),
              defaultVal: m.maps?.[raw] ?? 0,
              fieldPath: [c, f],
              fieldKind: fk,
              dynamicDefaultExpr: defObj,
            })
          }
        }
      }
    }
  }

  // Register items (lists of records/scalars)
  const itemMaps = new Set<string>()
  for (const [itemName, itemKind] of meta.items) {
    reg.slots.set(`${itemName}_len`, {kind: 'nat', ts: `${propAccess('state', itemName)}.length`, law: `${itemName}.length`})
    if (itemKind.kind === 'record') {
      for (const [f, fk] of itemKind.fields) {
        const raw = `${itemName}.${f}`
        itemMaps.add(raw)
        mapInfos.set(raw, {
          rawName: raw,
          mapName: itemName,
          stateExpr: propAccess('state', itemName),
          defaultVal: 0,
          fieldPath: [f],
          fieldKind: fk,
          dynamicDefaultExpr: kindDefaultTs(itemKind),
        })
      }
    } else {
      itemMaps.add(itemName)
      mapInfos.set(itemName, {
        rawName: itemName,
        mapName: itemName,
        stateExpr: propAccess('state', itemName),
        defaultVal: 0,
        fieldKind: itemKind,
        dynamicDefaultExpr: kindDefaultTs(itemKind),
      })
    }
  }

  // Print // gdp: law comments if in verifiable subset
  const stateLawComments: {name: string, expr: string}[] = []
  const stepLawComments: {name: string, expr: string}[] = []
  if (verifyReasons.length === 0) {
    for (let i = 0; i < laws.length; i++) {
      const l = laws[i]!
      const lctx: LawPrintCtx = {reg, flags: m.step.flags ?? {}, mapReads: lawMapReads, fns: m.fns ?? {}, step: false, boundKeys: new Set(l.forall ? [l.forall] : [])}
      const res = printLawCondition(l.holds, lctx, l.forall)
      if (!res.ok) { verifyReasons.push(`law "${l.name}": ${res.reason}`); continue }
      stateLawComments.push({name: l.name, expr: res.expr})
      reports[i] = {...reports[i]!, lawExpr: res.expr}
    }
    for (let i = 0; i < stepLaws.length; i++) {
      const sl = stepLaws[i]!
      const cond: C = sl.when && !Array.isArray(sl.when)
        ? {op: 'or', xs: [{op: 'not', x: sl.when}, sl.then]}
        : sl.then
      const lctx: LawPrintCtx = {reg: stepReg, flags: m.step.flags ?? {}, mapReads: lawMapReads, fns: m.fns ?? {}, step: true, boundKeys: new Set(sl.forall ? [sl.forall] : [])}
      const res = printLawCondition(cond, lctx, sl.forall)
      if (!res.ok) { verifyReasons.push(`step law "${sl.name}": ${res.reason}`); continue }
      stepLawComments.push({name: sl.name, expr: res.expr})
      reports[laws.length + i] = {...reports[laws.length + i]!, lawExpr: res.expr}
    }
  }
  const verifiable = verifyReasons.length === 0 && (stateLawComments.length + stepLawComments.length) === (laws.length + stepLaws.length) && (laws.length + stepLaws.length) > 0

  // Helper functions (div/mod emitted inline; recur and custom fns emitted as pure top-level helpers)
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

  // Special emission for map cell reads when cellKind is record or variant (avoid `?.`, use clean local or inline)
  const ctx: EmitCtx = {
    reg,
    mode: 'rule',
    flags: new Map(),
    maps: new Map(),
    fns: m.fns ?? {},
    helpers: new Set(),
    fnNames,
    boundKeys: new Map(),
    statePrefix: 'state',
  }
  // Wrap mapInfos for EmitCtx so record/variant/item accesses work with zero `?.`
  const cellGetters: string[] = []
  const cellGetterName = new Map<string, string>()
  for (const [mapName, , cellKind] of meta.maps) {
    if (!cellKind) {
      ctx.maps.set(mapName, mapInfos.get(mapName)!)
    } else if (cellKind.kind === 'record') {
      const def = kindDefaultTs(cellKind)
      for (const [f, fk] of cellKind.fields) {
        const raw = `${mapName}.${f}`
        // Map read returns `(state.Acct.get(k) ?? { ... }).f`
        ctx.maps.set(raw, {
          rawName: raw,
          mapName,
          stateExpr: propAccess('state', mapName),
          defaultVal: m.maps?.[raw] ?? 0,
          fieldKind: fk,
        })
        cellGetterName.set(raw, `((state.${mapName}.get(__K__) ?? ${def}).${f})`)
      }
    } else if (cellKind.kind === 'variant') {
      const def = kindDefaultTs(cellKind)
      ctx.maps.set(mapName, {
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
          cellGetterName.set(raw, `${gid}(state.${mapName}, __K__)`)
          cellGetters.push(
            `function ${gid}(m: ReadonlyMap<number, ${kindTsType(cellKind)}>, k: number): ${kindTsType(fk)} {`,
            `  const c = m.get(k)`,
            `  return c !== undefined && ${propAccess('c', cellKind.tagKey)} === ${JSON.stringify(c)} ? ${propAccess('c', f)} : ${kindDefaultTs(fk)}`,
            '}',
          )
        }
      }
    }
  }
  for (const [itemName, itemKind] of meta.items) {
    if (itemKind.kind === 'record') {
      for (const [f, fk] of itemKind.fields) {
        const raw = `${itemName}.${f}`
        const gid = safeVar('$item_', raw)
        cellGetterName.set(raw, `${gid}(state.${itemName}, __K__)`)
        cellGetters.push(
          `function ${gid}(xs: readonly ${kindTsType(itemKind)}[], k: number): ${kindTsType(fk)} {`,
          `  const c = xs[k]`,
          `  return c !== undefined ? ${propAccess('c', f)} : ${kindDefaultTs(fk)}`,
          '}',
        )
      }
    } else {
      const gid = safeVar('$item_', itemName)
      cellGetterName.set(itemName, `${gid}(state.${itemName}, __K__)`)
      cellGetters.push(
        `function ${gid}(xs: readonly ${kindTsType(itemKind)}[], k: number): ${kindTsType(itemKind)} {`,
        `  return xs[k] ?? ${kindDefaultTs(itemKind)}`,
        '}',
      )
    }
  }

  // Override emitTsCode's get lookup cleanly via a thin pre-pass or enhanced map reader:
  const em = emitRuleExprs(ctx, cellGetterName)

  // --- Emit `init(params)` ---
  const initReg = makeRegistry()
  for (const [n, , k] of meta.params) registerKind(initReg, n, k, propAccess('params', n), n)
  const initCtx: EmitCtx = {...ctx, reg: initReg, flags: new Map(), maps: new Map()}
  const initEm = emitRuleExprs(initCtx, new Map())

  const paramChecks = meta.params.flatMap(([n, , k]) => kindGuardChecks(k, propAccess('params', n), n, verifiable))
  const preExpr = m.pre ? initEm.emitCond(m.pre) : 'true'

  // --- Emit `step(params, state, input)` ---
  const inputChecks = meta.inputs.flatMap(([n, , k]) => kindGuardChecks(k, propAccess('input', n), n, verifiable))
  const historyFields = m.history ? {
    recordFields: m.history.record,
    sums: Object.entries(m.history.sums),
    queries: Object.entries(m.history.queries),
    keep: m.history.keep,
    prune: m.history.prune,
  } : undefined

  // If history exists, register query variables as locals in step
  if (historyFields) {
    for (const [qName] of historyFields.queries) {
      reg.slots.set(qName, {kind: 'nat', ts: safeVar('$q_', qName), law: qName})
    }
  }

  const flagLines: string[] = []
  for (const [fname, fc] of Object.entries(m.step.flags ?? {})) {
    const local = safeVar('$flag_', fname)
    flagLines.push(`  const ${local}: boolean = ${em.emitCond(fc)}`)
    ctx.flags.set(fname, local)
  }

  const assumeExpr = m.assume ? em.emitCond(m.assume) : 'true'
  const primFailExpr = m.primitiveFailure ? em.emitCond(m.primitiveFailure) : undefined

  // Scalar state updates
  const nextScalars: [string, string][] = []
  for (const [n, k] of meta.state) {
    if (historyFields && historyFields.sums.some(([sn]) => sn === n)) continue
    const val = em.emitKindVal(k, n, part => m.step.state?.[part] ?? {op: 'var', name: part})
    nextScalars.push([n, val])
  }

  // Map updates
  const mapUpdateLines: string[] = []
  const nextMapFields: [string, string][] = []
  for (const [mapName, dflt, cellKind] of meta.maps) {
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
        // Clean conditional set when else branch is identity get(mapName, key)
        if (w.value.op === 'if' && w.value.else.op === 'get' && w.value.else.map === mapName && sameNode(w.value.else.key, w.key)) {
          mapUpdateLines.push(`  if (${em.emitCond(w.value.c)}) { ${localMap}.set(${kExpr}, ${em.emitNum(w.value.then)}) }`)
        } else {
          mapUpdateLines.push(`  ${localMap}.set(${kExpr}, ${em.emitNum(w.value)})`)
        }
        nextMapFields.push([mapName, localMap])
        void dflt
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
        mapUpdateLines.push(
          `  const ${localMap} = new Map(${propAccess('state', mapName)})`,
          `  ${localMap}.set(${kExpr}, ${recVal})`,
        )
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
        mapUpdateLines.push(
          `  const ${localMap} = new Map(${propAccess('state', mapName)})`,
          `  ${localMap}.set(${kExpr}, ${varVal})`,
        )
        nextMapFields.push([mapName, localMap])
      }
    }
  }

  // Items (lists) updates
  const itemUpdateLines: string[] = []
  const nextItemFields: [string, string][] = []
  for (const [itemName, itemKind] of meta.items) {
    const localList = safeVar('next_', itemName)
    const lenE = m.step.state?.[`${itemName}_len`] ?? {op: 'var', name: `${itemName}_len`}
    const nextLenExpr = em.emitNum(lenE)
    const partNames = itemKind.kind === 'record' ? itemKind.fields.map(([f]) => `${itemName}.${f}`) : [itemName]
    const firstW = partNames.map(p => m.step.maps?.[p]).find(Boolean)
    itemUpdateLines.push(`  const ${localList} = [...${propAccess('state', itemName)}]`)
    if (firstW && 'key' in firstW) {
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
      itemUpdateLines.push(`  ${localList}.length = ${nextLenExpr}`)
    }
    nextItemFields.push([itemName, localList])
  }

  // History updates (for log/sums/queries/prune rules like `window`)
  const historyLines: string[] = []
  const nextHistoryFields: [string, string][] = []
  if (historyFields) {
    const recReg = makeRegistry()
    for (const [n, , k] of meta.params) registerKind(recReg, n, k, propAccess('params', n), n)
    for (const [n, , k] of meta.inputs) registerKind(recReg, n, k, propAccess('input', n), n)
    for (const rf of historyFields.recordFields) {
      const inEntry = meta.inputs.find(([n]) => n === rf)
      const k = inEntry ? inEntry[2] : {kind: 'nat' as const}
      registerKind(recReg, `r.${rf}`, k, propAccess('$rec', rf), `r.${rf}`)
    }
    const recCtx: EmitCtx = {...ctx, reg: recReg, flags: new Map(), maps: new Map()}
    const recEm = emitRuleExprs(recCtx, new Map())
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
      historyLines.push(
        `  let ${safeVar('$q_', qName)} = 0`,
        `  for (const $rec of $kept) ${safeVar('$q_', qName)} += ${recEm.emitNum(qE)}`,
      )
    }
    // Keep decision runs after flags! Emit keep + updated sums in postHistoryLines
    const recObj = `{ ${historyFields.recordFields.map(rf => `${propKey(rf)}: ${propAccess('input', rf)}`).join(', ')} }`
    nextHistoryFields.push(['_history', '$nextHistory'])
    if (historyFields.prune) nextHistoryFields.push(['_last', propAccess('input', historyFields.prune.order)])
    // We'll emit the post-flag history sum updates right after flagLines
    void recObj
  }

  const arithDesc = hasDecimals
    ? 'exact scaled fixed-point integers; safe range <= 2^53 - 1'
    : 'exact JavaScript safe integers over N/Z (truncated natural subtraction max(0, a - b); safe range <= 2^53 - 1)'

  const lines: string[] = [
    ...renderHeader({name: meta.name, kind, digest, arithmetic: arithDesc, laws: reports}),
    '',
  ]

  // Types
  if (hasParams) {
    lines.push('export type Params = {')
    for (const [n, , k] of meta.params) lines.push(`  readonly ${propKey(n)}: ${kindTsType(k)}`)
    lines.push('}', '')
  } else {
    lines.push('export type Params = Record<string, never>', '')
  }

  if (hasInputs) {
    lines.push('export type Input = {')
    for (const [n, , k] of meta.inputs) lines.push(`  readonly ${propKey(n)}: ${kindTsType(k)}`)
    lines.push('}', '')
  } else {
    lines.push('export type Input = Record<string, never>', '')
  }

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
    const valType = cellKind ? kindTsType(cellKind) : 'number'
    lines.push(`  readonly ${propKey(mapName)}: Map<number, ${valType}>`)
    if (!cellKind && eachMaps.has(mapName)) lines.push(`  readonly ${propKey(`${mapName}_default`)}: number`)
  }
  for (const [itemName, itemKind] of meta.items) {
    lines.push(`  readonly ${propKey(itemName)}: readonly ${kindTsType(itemKind)}[]`)
  }
  if (historyFields) {
    lines.push('  readonly _history: readonly HistoryRecord[]')
    if (historyFields.prune) lines.push('  readonly _last: number')
  }
  lines.push('}', '')

  // Helpers
  const helperLines = renderHelpers(ctx.helpers)
  if (helperLines.length) lines.push(...helperLines, '')
  if (fnHelperLines.length) lines.push(...fnHelperLines, '')
  if (cellGetters.length) lines.push(...cellGetters, '')

  // init(params)
  const initBodyLines: string[] = []
  if (paramChecks.length) initBodyLines.push(`  if (${paramChecks.join(' || ')}) throw new RangeError(${JSON.stringify(`${meta.name}: invalid params`)})`)
  if (preExpr !== 'true') initBodyLines.push(`  if (!(${preExpr})) throw new RangeError(${JSON.stringify(`${meta.name}: params violate precondition`)})`)
  initBodyLines.push('  return {')
  for (const [n, k] of meta.state) {
    const val = initEm.emitKindVal(k, n, part => m.state[part] ?? {op: 'const', value: 0})
    initBodyLines.push(`    ${propKey(n)}: ${val},`)
  }
  for (const [mapName, dflt, cellKind] of meta.maps) {
    initBodyLines.push(`    ${propKey(mapName)}: new Map(),`)
    if (!cellKind && eachMaps.has(mapName)) initBodyLines.push(`    ${propKey(`${mapName}_default`)}: ${dflt},`)
  }
  for (const [itemName] of meta.items) initBodyLines.push(`    ${propKey(itemName)}: [],`)
  if (historyFields) {
    initBodyLines.push('    _history: [],')
    if (historyFields.prune) initBodyLines.push('    _last: 0,')
  }
  initBodyLines.push('  }')
  const initUsesParams = initBodyLines.some(l => /\bparams\b/.test(l))
  const initParamSig = hasParams ? (initUsesParams ? 'params: Params' : '_params: Params') : '_params: Params = {}'
  lines.push(`export function init(${initParamSig}): State {`, ...initBodyLines, '}', '')

  // step(params, state, input)
  const stepBodyLines: string[] = []
  if (inputChecks.length) stepBodyLines.push(`  if (${inputChecks.join(' || ')}) throw new RangeError(${JSON.stringify(`${meta.name}: invalid input`)})`)
  stepBodyLines.push(...historyLines)
  stepBodyLines.push(...flagLines)
  if (assumeExpr !== 'true') stepBodyLines.push(`  if (!(${assumeExpr})) throw new RangeError(${JSON.stringify(`${meta.name}: input violates assumption`)})`)
  if (primFailExpr && primFailExpr !== 'false') {
    stepBodyLines.push(`  if (${primFailExpr}) throw new RangeError(${JSON.stringify(`${meta.name}: arithmetic trap`)})`)
  }
  for (const [n, expr] of nextScalars) stepBodyLines.push(`  const ${safeVar('next_', n)} = ${expr}`)
  stepBodyLines.push(...mapUpdateLines)
  stepBodyLines.push(...itemUpdateLines)

  if (historyFields) {
    const recReg = makeRegistry()
    for (const [n, , k] of meta.params) registerKind(recReg, n, k, propAccess('params', n), n)
    for (const [n, , k] of meta.inputs) registerKind(recReg, n, k, propAccess('input', n), n)
    for (const rf of historyFields.recordFields) {
      const k = meta.inputs.find(([n]) => n === rf)?.[2] ?? {kind: 'nat' as const}
      registerKind(recReg, `r.${rf}`, k, propAccess('$rec', rf), `r.${rf}`)
    }
    const recEm = emitRuleExprs({...ctx, reg: recReg, flags: new Map(), maps: new Map()}, new Map())
    const keepExpr = em.emitCond(historyFields.keep)
    const recObj = `{ ${historyFields.recordFields.map(rf => `${propKey(rf)}: ${propAccess('input', rf)}`).join(', ')} }`
    stepBodyLines.push(`  const $nextHistory = (${keepExpr}) ? [...$kept, ${recObj}] : $kept`)
    for (const [sName, sE] of historyFields.sums) {
      stepBodyLines.push(
        `  let ${safeVar('next_', sName)} = 0`,
        `  for (const $rec of $nextHistory) ${safeVar('next_', sName)} += ${recEm.emitNum(sE)}`,
      )
    }
  }

  stepBodyLines.push('  return {')
  for (const [n] of meta.state) stepBodyLines.push(`    ${propKey(n)}: ${safeVar('next_', n)},`)
  for (const [n, expr] of nextMapFields) stepBodyLines.push(`    ${propKey(n)}: ${expr},`)
  for (const [n, expr] of nextItemFields) stepBodyLines.push(`    ${propKey(n)}: ${expr},`)
  for (const [n, expr] of nextHistoryFields) stepBodyLines.push(`    ${propKey(n)}: ${expr},`)
  stepBodyLines.push('  }')
  const stepUsesParams = stepBodyLines.some(l => /\bparams\b/.test(l))
  const stepUsesState = stepBodyLines.some(l => /\bstate\b/.test(l))
  const stepUsesInput = stepBodyLines.some(l => /\binput\b/.test(l))
  const stepParamArg = stepUsesParams ? 'params: Params' : '_params: Params'
  const stepStateArg = stepUsesState ? 'state: State' : '_state: State'
  const stepInputArg = stepUsesInput ? 'input: Input' : '_input: Input'
  lines.push(`export function step(${stepParamArg}, ${stepStateArg}, ${stepInputArg}): State {`, ...stepBodyLines, '}')

  // Thin runner class for TS reader verification (`gdp-wired emit --verify` / `gdp-wired check`)
  if (verifiable) {
    lines.push('')
    for (const l of stateLawComments) lines.push(`// gdp: law ${sanitizeComment(l.name)}: ${l.expr}`)
    lines.push(`export class ${className} {`)
    for (const [n, , k] of meta.params) lines.push(`  readonly ${n}: ${kindTsType(k)}`)
    for (const [n, k] of meta.state) lines.push(`  ${n}: ${kindTsType(k)}`)
    for (const [mapName, , cellKind] of meta.maps) {
      lines.push(`  ${mapName}: Map<number, ${cellKind ? kindTsType(cellKind) : 'number'}>`)
    }
    const ctorSig = meta.params.map(([n, , k]) => `${n}: ${kindTsType(k)}`).join(', ')
    lines.push('', `  constructor(${ctorSig}) {`)
    if (hasParams) {
      for (const [n] of meta.params) lines.push(`    this.${n} = ${n}`)
    }
    const paramsObj = hasParams ? `{ ${meta.params.map(([n]) => n).join(', ')} }` : '{}'
    if (meta.state.length > 0) {
      lines.push(`    const st = init(${paramsObj})`)
      for (const [n] of meta.state) lines.push(`    this.${n} = st.${n}`)
    } else if (hasParams || preExpr !== 'true') {
      lines.push(`    init(${paramsObj})`)
    }
    // Map fields MUST be initialized with `new Map()` directly in the constructor for readClass's mapInits!
    for (const [mapName] of meta.maps) lines.push(`    this.${mapName} = new Map()`)
    lines.push('  }', '')
    for (const sl of stepLawComments) lines.push(`  // gdp: law ${sanitizeComment(sl.name)}: ${sl.expr}`)
    const methodSig = hasInputs ? 'input: Input' : ''
    lines.push(`  step(${methodSig}): void {`)
    const callParams = hasParams ? `{ ${meta.params.map(([n]) => `${n}: this.${n}`).join(', ')} }` : '{}'
    const stateFields = [...meta.state.map(([n]) => `${n}: this.${n}`), ...meta.maps.map(([n]) => `${n}: this.${n}`)].join(', ')
    const callInput = hasInputs ? 'input' : '{}'
    lines.push(`    const next = step(${callParams}, { ${stateFields} }, ${callInput})`)
    for (const [n] of meta.state) lines.push(`    this.${n} = next.${n}`)
    for (const [mapName] of meta.maps) lines.push(`    this.${mapName} = next.${mapName}`)
    lines.push('  }', '}')
  }

  lines.push('')
  return {
    source: lines.join('\n'),
    digest,
    version: GDP_WIRED_VERSION,
    name: meta.name,
    kind,
    laws: reports,
    allProven,
    verify: {
      verifiable,
      ...(verifiable ? {entry: className, ...(opts.from ? {from: opts.from} : {})} : {}),
      expectedLaws: verifiable ? [...stateLawComments.map(l => l.name), ...stepLawComments.map(l => l.name)] : [],
      reasons: verifyReasons,
    },
  }
}

// Helper for emitRule to support record/variant/item map getters cleanly
function emitRuleExprs(ctx: EmitCtx, cellGetters: Map<string, string>) {
  const base = emitTsCode(ctx)
  if (cellGetters.size === 0) return base
  // Patch map reads through cellGetters via wrapper emitter
  const patchGet = (e: E): E => e
  void patchGet
  // Build custom emitter that checks cellGetters on 'get'
  const origMaps = ctx.maps
  const patchedCtx: EmitCtx = {
    ...ctx,
    maps: new Map(origMaps),
  }
  const inner = emitTsCode(patchedCtx)
  const replaceGetsNum = (e: E): string => {
    switch (e.op) {
      case 'get': {
        const tpl = cellGetters.get(e.map)
        if (tpl) {
          const kTs = replaceGetsNum(e.key)
          const raw = tpl.replace('__K__', kTs)
          const fk = origMaps.get(e.map)?.fieldKind
          if (fk?.kind === 'bool') return `(${raw} ? 1 : 0)`
          if (fk?.kind === 'oneOf') {
            ctx.helpers.add('idx')
            return `$idx(${raw}, [${fk.values.map(v => JSON.stringify(v)).join(', ')}])`
          }
          return raw
        }
        return inner.emitNum(e)
      }
      case 'add': return `(${replaceGetsNum(e.a)} + ${replaceGetsNum(e.b)})`
      case 'sub': return `Math.max(0, ${replaceGetsNum(e.a)} - ${replaceGetsNum(e.b)})`
      case 'mul': return e.k === 1 ? replaceGetsNum(e.a) : `(${e.k} * ${replaceGetsNum(e.a)})`
      case 'prod': return `(${replaceGetsNum(e.a)} * ${replaceGetsNum(e.b)})`
      case 'min': return `Math.min(${replaceGetsNum(e.a)}, ${replaceGetsNum(e.b)})`
      case 'max': return `Math.max(${replaceGetsNum(e.a)}, ${replaceGetsNum(e.b)})`
      case 'if': return `(${replaceGetsCond(e.c)} ? ${replaceGetsNum(e.then)} : ${replaceGetsNum(e.else)})`
      default: return inner.emitNum(e)
    }
  }
  const replaceGetsCond = (c: C): string => {
    switch (c.op) {
      case '<': case '<=': case '=': {
        // Check bool/choice cellGetter equality
        if (c.op === '=') {
          if (c.a.op === 'get' && cellGetters.has(c.a.map) && c.b.op === 'const') {
            const fk = origMaps.get(c.a.map)?.fieldKind
            const expr = cellGetters.get(c.a.map)!.replace('__K__', replaceGetsNum(c.a.key))
            if (fk?.kind === 'bool' && (c.b.value === 0 || c.b.value === 1)) return c.b.value === 1 ? expr : `!(${expr})`
            if (fk?.kind === 'oneOf' && c.b.value >= 0 && c.b.value < fk.values.length) return `(${expr} === ${JSON.stringify(fk.values[c.b.value]!)})`
          }
          if (c.b.op === 'get' && cellGetters.has(c.b.map) && c.a.op === 'const') {
            const fk = origMaps.get(c.b.map)?.fieldKind
            const expr = cellGetters.get(c.b.map)!.replace('__K__', replaceGetsNum(c.b.key))
            if (fk?.kind === 'bool' && (c.a.value === 0 || c.a.value === 1)) return c.a.value === 1 ? expr : `!(${expr})`
            if (fk?.kind === 'oneOf' && c.a.value >= 0 && c.a.value < fk.values.length) return `(${expr} === ${JSON.stringify(fk.values[c.a.value]!)})`
          }
        }
        const op = c.op === '=' ? '===' : c.op
        // If neither side touches cellGetters, use inner's signed-canceling emitCond!
        const touches = (x: E): boolean => x.op === 'get' ? cellGetters.has(x.map) || touches(x.key) : 'a' in x && typeof x.a === 'object' ? touches(x.a) || ('b' in x && typeof x.b === 'object' && touches(x.b)) : x.op === 'if' ? touches(x.then) || touches(x.else) : false
        if (!touches(c.a) && !touches(c.b)) return inner.emitCond(c)
        return `(${replaceGetsNum(c.a)} ${op} ${replaceGetsNum(c.b)})`
      }
      case 'not': {
        if (c.x.op === 'not') return replaceGetsCond(c.x.x)
        const s = replaceGetsCond(c.x)
        return s === 'true' ? 'false' : s === 'false' ? 'true' : `!(${s})`
      }
      case 'and': {
        const parts = c.xs.map(replaceGetsCond).filter(x => x !== 'true')
        if (parts.includes('false')) return 'false'
        return parts.length === 0 ? 'true' : parts.length === 1 ? parts[0]! : `(${parts.join(' && ')})`
      }
      case 'or': {
        const parts = c.xs.map(replaceGetsCond).filter(x => x !== 'false')
        if (parts.includes('true')) return 'true'
        return parts.length === 0 ? 'false' : parts.length === 1 ? parts[0]! : `(${parts.join(' || ')})`
      }
      case 'flag': return inner.emitCond(c)
      case 'all': return inner.emitCond(c)
    }
  }
  const replaceGetsBool = (e: E): string => {
    if (e.op === 'const') return e.value === 0 ? 'false' : 'true'
    if (e.op === 'get' && cellGetters.has(e.map) && origMaps.get(e.map)?.fieldKind?.kind === 'bool') {
      return cellGetters.get(e.map)!.replace('__K__', replaceGetsNum(e.key))
    }
    if (e.op === 'if') {
      if (e.then.op === 'const' && e.then.value === 1 && e.else.op === 'const' && e.else.value === 0) return replaceGetsCond(e.c)
      if (e.then.op === 'const' && e.then.value === 0 && e.else.op === 'const' && e.else.value === 1) return replaceGetsCond({op: 'not', x: e.c})
      return `(${replaceGetsCond(e.c)} ? ${replaceGetsBool(e.then)} : ${replaceGetsBool(e.else)})`
    }
    return inner.emitBoolVal(e)
  }
  const replaceGetsChoice = (e: E, values: readonly string[]): string => {
    if (e.op === 'const' && e.value >= 0 && e.value < values.length) return JSON.stringify(values[e.value]!)
    if (e.op === 'get' && cellGetters.has(e.map) && origMaps.get(e.map)?.fieldKind?.kind === 'oneOf') {
      return cellGetters.get(e.map)!.replace('__K__', replaceGetsNum(e.key))
    }
    if (e.op === 'if') return `(${replaceGetsCond(e.c)} ? ${replaceGetsChoice(e.then, values)} : ${replaceGetsChoice(e.else, values)})`
    return inner.emitChoiceVal(e, values)
  }
  const replaceGetsKind = (k: KindInfo, baseName: string, getE: (part: string) => E): string => {
    switch (k.kind) {
      case 'nat': case 'unknown': return replaceGetsNum(getE(baseName))
      case 'bool': return replaceGetsBool(getE(baseName))
      case 'oneOf': return replaceGetsChoice(getE(baseName), k.values)
      case 'record': return `{ ${k.fields.map(([f, fk]) => `${propKey(f)}: ${replaceGetsKind(fk, `${baseName}.${f}`, getE)}`).join(', ')} }`
      case 'variant': {
        const tagE = getE(baseName)
        const walk = (t: E, branch: (e: E) => E): string => {
          if (t.op === 'if') {
            return `(${replaceGetsCond(t.c)} ? ${walk(t.then, e => (e.op === 'if' && sameNode(e.c, t.c) ? branch(e.then) : branch(e)))} : ${walk(t.else, e => (e.op === 'if' && sameNode(e.c, t.c) ? branch(e.else) : branch(e)))})`
          }
          if (t.op === 'get' && origMaps.get(t.map)?.fieldKind?.kind === 'variant') {
            const info = origMaps.get(t.map)!
            return `(${info.stateExpr}.get(${replaceGetsNum(t.key)}) ?? ${info.dynamicDefaultExpr ?? kindDefaultTs(k)})`
          }
          if (t.op === 'const' && t.value >= 0 && t.value < k.cases.length) {
            const [cName, fs] = k.cases[t.value]!
            const fStr = fs.map(([f, fk]) => `${propKey(f)}: ${replaceGetsKind(fk, `${baseName}.${cName}.${f}`, part => branch(getE(part)))}`).join(', ')
            return `{ ${propKey(k.tagKey)}: ${JSON.stringify(cName)}${fStr ? `, ${fStr}` : ''} }`
          }
          return inner.emitKindVal(k, baseName, getE)
        }
        return walk(tagE, e => e)
      }
      default: return inner.emitKindVal(k, baseName, getE)
    }
  }
  return {...inner, emitNum: replaceGetsNum, emitCond: replaceGetsCond, emitBoolVal: replaceGetsBool, emitChoiceVal: replaceGetsChoice, emitKindVal: replaceGetsKind}
}

// --- emitRatRule -----------------------------------------------------------------------------------------------------

export function emitRatRule(r: RatRule<string, string, string>, opts: EmitRatOptions = {}): EmitResult {
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
    }),
    '',
    'export type Rat = readonly [bigint, bigint]',
    'export type RatInput = Rat | bigint | number | string',
    '',
    hasParams
      ? `export type Params = {\n${meta.params.map(([n]) => `  readonly ${propKey(n)}: Rat`).join('\n')}\n}`
      : 'export type Params = Record<string, never>',
    '',
    hasInputs
      ? `export type Input = {\n${meta.inputs.map(([n]) => `  readonly ${propKey(n)}: Rat`).join('\n')}\n}`
      : 'export type Input = Record<string, never>',
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
    '  if (den === 0n) throw new RangeError(\'rational denominator cannot be 0\')',
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
  const initUsesP = initBody.some(l => /\bparams\b/.test(l))
  const initSig = hasParams ? (initUsesP ? 'params: Params' : '_params: Params') : '_params: Params = {}'
  lines.push(`export function init(${initSig}): State {`, ...initBody, '}', '')

  // allowed
  const allowExpr = m.assume ? emitQC(m.assume, 'step') : 'true'
  const allowP = /\bparams\b/.test(allowExpr) ? 'params: Params' : '_params: Params'
  const allowS = /\bstate\b/.test(allowExpr) ? 'state: State' : '_state: State'
  const allowI = /\binput\b/.test(allowExpr) ? 'input: Input' : '_input: Input'
  lines.push(`export function allowed(${allowP}, ${allowS}, ${allowI}): boolean {`, `  return ${allowExpr}`, '}', '')

  // step
  const stepBody: string[] = []
  const stateFields = meta.state.map(s => {
    const upd = m.step[s]
    return `    ${propKey(s)}: ${upd ? emitQE(upd, 'step') : propAccess('state', s)},`
  })
  const stepUsesP = stateFields.some(l => /\bparams\b/.test(l)) || !!m.assume
  const stepUsesS = stateFields.some(l => /\bstate\b/.test(l)) || !!m.assume
  const stepUsesI = stateFields.some(l => /\binput\b/.test(l)) || !!m.assume
  const stepP = stepUsesP ? 'params: Params' : '_params: Params'
  const stepS = stepUsesS ? 'state: State' : '_state: State'
  const stepI = stepUsesI ? 'input: Input' : '_input: Input'
  if (m.assume) stepBody.push(`  if (!allowed(params, state, input)) throw new RangeError(${JSON.stringify(`${meta.name}: input violates assumption`)})`)
  stepBody.push('  return {', ...stateFields, '  }')
  lines.push(`export function step(${stepP}, ${stepS}, ${stepI}): State {`, ...stepBody, '}', '')

  // Filter out unused $min/$max/$mul/$add/$sub helpers so oxlint never flags unused functions!
  const rawSource = lines.join('\n')
  const cleanedLines = lines.filter(line => {
    const fm = /^function (\$(?:add|sub|mul|cmp|min|max))\b/.exec(line)
    if (!fm) return true
    const fnName = fm[1]!
    // Count occurrences in rawSource; if only 1 (its own definition), drop it!
    const count = rawSource.split(fnName).length - 1
    return count > 1
  })

  return {
    source: cleanedLines.join('\n'),
    digest,
    version: GDP_WIRED_VERSION,
    name: meta.name,
    kind: 'ratRule',
    laws: reports,
    allProven,
    verify: {
      verifiable: false,
      expectedLaws: [],
      reasons: ['RatRule uses exact BigInt rational arithmetic over Q, which the TypeScript integer reader does not support'],
    },
  }
}
