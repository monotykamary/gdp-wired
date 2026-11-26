// Emit self-contained, zero-dependency TypeScript source from proven gdp-wired rules, functions, rational rules and
// statecharts. Generated code has zero imports, zero dynamic code generation, and zero proof/kernel runtime.
// Header comments record the rule name, version, canonical machine digest, exact arithmetic semantics, and every
// law's proof status. Differential verification (`gdp-wired emit --verify`) tests the emitted module directly against
// the proven rule's interpreter on exhaustive small domains and randomized runs.
import {
  type Fold,
  type Loop,
  type QMachine,
  type QLaw,
  type StepLaw,
  boundOf,
  crossFree,
  eachParts,
  finiteBound,
  mapArities,
  plainKey,
  sumRuntime,
} from '../kernel/kernel.ts'
import {parseWordDivisionName, wordDivisionArgs} from '../kernel/word-division.ts'
import {
  type Breaks,
  type C,
  type DirectFn,
  type E,
  type Fn,
  type Law,
  type Machine,
  breaksOf,
  directOf,
  joinOf,
  mapsIn,
  pairedArgs,
  recomputedSums,
  unreachable,
  walk,
} from './machine.ts'
import {
  type Decision,
  type FoldRule,
  type Fun,
  type KindInfo,
  type LoopRule,
  type ProveOptions,
  type Raw,
  type RoseFold,
  type Rule,
  type RuleMeta,
  type Verdict,
  Unproven,
  funOf,
  inspectFoldMeta,
  inspectFunMeta,
  inspectLoopMeta,
  inspectRuleMeta,
  interned,
  proveDecision,
  proveFold,
  proveLoop,
  proveRule,
  proveSteps,
} from './dsl.ts'
import {type RatLaw, type RatRule, inspectRatRule, proveRatRule} from './rationals.ts'
import {type Chart, inspectChart} from './chart.ts'
import {type EmitHelper, createPrinter, createQPrinter, renderTypedHelpers} from './codegen.ts'
import {sha256Hex} from './sha256.ts'
export {sha256Hex} from './sha256.ts'

export const GDP_WIRED_VERSION = '0.62.0'

// Compile-time exhaustive Kind and Machine-part tables: adding any new KindInfo variant or Machine property fails `tsc`.
const KIND_INFO_TABLE: Record<KindInfo['kind'], true> = {
  nat: true, bool: true, oneOf: true, int: true, decimal: true, maybe: true,
  record: true, variant: true, str: true, fixed: true, unknown: true,
}
export const KIND_NAMES = Object.keys(KIND_INFO_TABLE) as readonly KindInfo['kind'][]
const EMIT_MACHINE_PARTS: Record<keyof Machine, true> = {
  name: true, params: true, inputs: true, state: true, maps: true, inputMaps: true,
  step: true, pre: true, assume: true, primitiveFailure: true, history: true,
  sums: true, counts: true, leasts: true, fns: true, facts: true, relations: true,
}
void EMIT_MACHINE_PARTS

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyRule = Rule<any, any, any, any, any, any, any, any>
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyFun = Fun<any, any, any>
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyRatRule = RatRule<any, any, any>
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyChart = Chart<any, any, any>
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyFold = FoldRule<any, any, any> | RoseFold<any, any, any, any>
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyLoop = LoopRule<any, any, any>

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
  readonly kind: 'rule' | 'fun' | 'ratRule' | 'chart' | 'fold' | 'loop'
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

export type EmitFoldOptions = {
  laws?: readonly Law[]
  name?: string
  allowUnproven?: boolean
  provenance?: EmitProvenance
}

export type EmitLoopOptions = {
  laws?: readonly Law[]
  name?: string
  ms?: number
  allowUnproven?: boolean
  provenance?: EmitProvenance
}

export type EmitBundle =
  | {readonly rule: AnyRule, readonly laws?: readonly Law[], readonly stepLaws?: readonly StepLaw[], readonly name?: string, readonly from?: 'any', readonly ms?: number}
  | {readonly fun: AnyFun, readonly laws?: readonly Decision[], readonly name?: string, readonly defaultParams?: Readonly<Record<string, Raw>>, readonly ms?: number}
  | {readonly ratRule: AnyRatRule, readonly laws?: readonly RatLaw<string, string>[], readonly name?: string, readonly ms?: number}
  | {readonly chart: AnyChart, readonly laws?: readonly Law[], readonly stepLaws?: readonly StepLaw[], readonly name?: string, readonly from?: 'any', readonly ms?: number}
  | {readonly fold: AnyFold, readonly laws?: readonly Law[], readonly name?: string, readonly ms?: number}
  | {readonly loop: AnyLoop, readonly laws?: readonly Law[], readonly name?: string, readonly ms?: number}

// --- Canonical machine digest (SHA-256 lives in core/sha256.ts) ------------------------------------------------------

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
    ...(m.relations ? {relations: m.relations} : {}),
    ...(m.fns ? {fns: Object.fromEntries(Object.entries(m.fns).map(([k, f]) => [k, stripFnMeta(f)]))} : {}),
  }
  return `sha256:${sha256Hex(canonicalJson(norm))}`
}

export function qMachineDigest(m: QMachine): string {
  return `sha256:${sha256Hex(canonicalJson(m))}`
}

export function foldDigest(f: Fold): string {
  return `sha256:${sha256Hex(canonicalJson(f))}`
}

export function loopDigest(l: Loop): string {
  return `sha256:${sha256Hex(canonicalJson(l))}`
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
    default: return unreachable(k)
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
    default: return unreachable(k)
  }
}

function rawToTsLiteral(val: Raw | undefined, k: KindInfo): string {
  if (val === undefined) return kindDefaultTs(k)
  switch (k.kind) {
    case 'nat': case 'int': case 'decimal': case 'unknown': return typeof val === 'number' ? String(val) : '0'
    case 'bool': return val ? 'true' : 'false'
    case 'oneOf': return JSON.stringify(typeof val === 'string' ? val : k.values[0]!)
    case 'maybe': return val === null ? 'null' : rawToTsLiteral(val, k.of)
    case 'record': {
      const obj = (val && typeof val === 'object' ? val : {}) as Record<string, Raw>
      return `{ ${k.fields.map(([f, fk]) => `${propKey(f)}: ${rawToTsLiteral(obj[f], fk)}`).join(', ')} }`
    }
    case 'variant': {
      const obj = (val && typeof val === 'object' ? val : {}) as Record<string, Raw>
      const tag = typeof obj[k.tagKey] === 'string' ? obj[k.tagKey] as string : k.cases[0]![0]
      const found = k.cases.find(([c]) => c === tag) ?? k.cases[0]!
      const rest = found[1].map(([f, fk]) => `${propKey(f)}: ${rawToTsLiteral(obj[f], fk)}`).join(', ')
      return `{ ${propKey(k.tagKey)}: ${JSON.stringify(found[0])}${rest ? `, ${rest}` : ''} }`
    }
    case 'str': return typeof val === 'string' ? (val === '' ? "''" : JSON.stringify(val)) : "''"
    case 'fixed': return k.width === 64 ? JSON.stringify(typeof val === 'string' || typeof val === 'number' || typeof val === 'bigint' ? String(val) : '0') : String(Number(val))
    default: return unreachable(k)
  }
}

function emitCellEq(k: KindInfo, a: string, b: string): string {
  switch (k.kind) {
    case 'nat': case 'int': case 'decimal': case 'bool': case 'oneOf': case 'str': case 'fixed': case 'unknown':
      return `(${a} === ${b})`
    case 'maybe':
      return `(${a} === ${b} || (${a} !== null && ${b} !== null && ${emitCellEq(k.of, a, b)}))`
    case 'record':
      return k.fields.length ? `(${k.fields.map(([f, fk]) => emitCellEq(fk, propAccess(a, f), propAccess(b, f))).join(' && ')})` : 'true'
    case 'variant':
      return `(${k.cases.map(([c, fs]) => `(${propAccess(a, k.tagKey)} === ${JSON.stringify(c)} && ${propAccess(b, k.tagKey)} === ${JSON.stringify(c)}${fs.length ? ` && ${fs.map(([f, fk]) => emitCellEq(fk, propAccess(a, f), propAccess(b, f))).join(' && ')}` : ''})`).join(' || ')})`
    default: return unreachable(k)
  }
}

function emitFixedPrep(rawName: string, kind: KindInfo, tsExpr: string, helpers: Set<EmitHelper>, lines: string[], guard?: string): void {
  switch (kind.kind) {
    case 'fixed': {
      helpers.add('fixedLimbs')
      const arr = safeVar('$fl_', rawName)
      const call = `$fixedLimbs(${tsExpr}, ${kind.width}, ${kind.signed}, ${JSON.stringify(rawName)})`
      const limbs = kind.width === 8 ? 1 : kind.width / 16
      lines.push(`  const ${arr} = ${guard ? `(${guard} ? ${call} : [${Array.from({length: limbs}, () => '0').join(', ')}])` : call}`)
      for (let i = 0; i < limbs; i++) lines.push(`  const ${safeVar('$limb_', rawName)}_${i} = ${arr}[${i}]!`)
      return
    }
    case 'maybe': {
      const innerGuard = guard ? `${guard} && ${tsExpr} !== null` : `${tsExpr} !== null`
      emitFixedPrep(rawName, kind.of, tsExpr, helpers, lines, innerGuard)
      return
    }
    case 'record':
      for (const [f, fk] of kind.fields) emitFixedPrep(`${rawName}.${f}`, fk, propAccess(tsExpr, f), helpers, lines, guard)
      return
    case 'variant':
      for (const [c, fs] of kind.cases) {
        const cg = guard ? `${guard} && ${propAccess(tsExpr, kind.tagKey)} === ${JSON.stringify(c)}` : `${propAccess(tsExpr, kind.tagKey)} === ${JSON.stringify(c)}`
        for (const [f, fk] of fs) emitFixedPrep(`${rawName}.${c}.${f}`, fk, propAccess(tsExpr, f), helpers, lines, cg)
      }
      return
    case 'nat': case 'bool': case 'oneOf': case 'int': case 'decimal': case 'str': case 'unknown':
      return
    default: return unreachable(kind)
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
    default: return unreachable(k)
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
    default: return unreachable(e)
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
    default: return unreachable(kind)
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
  readonly helpers: Set<EmitHelper>
  readonly fnNames: Map<string, string>
  readonly boundKeys: Map<string, string>
  readonly cse: Map<string, {ts: string, kind: KindInfo}>
  usesMapsView?: boolean
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
      default: return unreachable(s)
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
    const wd = parseWordDivisionName(map)
    if (wd) {
      const args = wordDivisionArgs(key, wd.width)
      if (!args) throw new Error(`${map}: invalid word division tuple key`)
      ctx.helpers.add('wordDiv')
      return `$wordDiv(${wd.width}, ${JSON.stringify(wd.part)}, ${wd.index}, [${args.map(emitNum).join(', ')}])`
    }
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

  const isPlainMapName = (mp: string): boolean => !ctx.fns[mp] && !/^(div|mod)\$\d+$/.test(mp) && !parseWordDivisionName(mp)

  const emitBreaksExpr = (b: Breaks): string => {
    ctx.helpers.add('breaks')
    ctx.usesMapsView = true
    const reads = b.reads.map(r => `[${JSON.stringify(r.map)}, ${r.off ? emitNum(r.off) : '0'}, ${r.minus}${r.part ? `, [${r.part[0]}, ${r.part[1]}]` : ''}]`).join(', ')
    const cmps = b.cmps.map(c => `[${emitNum(c.value)}, ${c.off ? emitNum(c.off) : '0'}, ${c.minus}]`).join(', ')
    return `$breaks($maps, [${reads}], [${cmps}])`
  }

  const emitKeysExpr = (t: E | C, key: string): string => {
    if (plainKey(t, key)) {
      ctx.helpers.add('keys')
      ctx.usesMapsView = true
      const ms = mapsIn(t).filter(isPlainMapName)
      return `$keys($maps, ${JSON.stringify(ms)})`
    }
    return emitBreaksExpr(breaksOf(t, key))
  }

  const emitTupleKeysExpr = (c: Extract<C, {op: 'all'}>): string => {
    const names = boundOf(c)
    if (names.every(n => plainKey(c.c, n))) {
      ctx.helpers.add('keys')
      ctx.usesMapsView = true
      const ms = mapsIn(c.c).filter(isPlainMapName)
      return `$keys($maps, ${JSON.stringify(ms)})`
    }
    const body = crossFree(c.c, names)
    if (names.every(n => plainKey(body, n))) {
      ctx.helpers.add('keys')
      ctx.helpers.add('spread')
      ctx.usesMapsView = true
      const ms = mapsIn(c.c).filter(isPlainMapName)
      return `$spread([0, ...$keys($maps, ${JSON.stringify(ms)})], ${names.length + 1})`
    }
    ctx.helpers.add('spread')
    const parts = names.map(n => breaksOf(body, n))
    return `$spread(${emitBreaksExpr({reads: parts.flatMap(b => b.reads), cmps: parts.flatMap(b => b.cmps)})}, ${names.length})`
  }

  const {printE: emitNum, printC: emitCond} = createPrinter({
    preExpr: e => {
      if (!ctx.cse.size) return undefined
      const hit = ctx.cse.get(JSON.stringify(e))
      return hit?.kind.kind === 'nat' ? hit.ts : undefined
    },
    onVar: slotAsNum,
    onAdd: (a, b) => {
      const lin = emptyLin()
      addLin(lin, a, 1)
      addLin(lin, b, 1)
      cancelSigned(lin, ctx.reg.signedVars)
      return formatLin(lin)
    },
    simplifyMul: true,
    onPair: (a, b) => { ctx.helpers.add('cpair'); return `$cpair(${a}, ${b})` },
    onProj: (a, k) => { ctx.helpers.add('cunpair'); return `$cunpair(${a})[${k}]` },
    onGet: (map, key) => {
      const fnExpr = emitFnCall(map, key)
      if (fnExpr !== undefined) return fnExpr
      const r = mapReadExpr(map, key)
      if (r.kind.kind === 'bool') return `(${r.expr} ? 1 : 0)`
      if (r.kind.kind === 'oneOf') {
        ctx.helpers.add('idx')
        return `$idx(${r.expr}, [${r.kind.values.map(v => JSON.stringify(v)).join(', ')}])`
      }
      return r.expr
    },
    onCmp: (op, a, b, negated) => emitCmp(op, a, b, negated),
    onNot: (x, printC) => {
      if (x.op === 'not') return printC(x.x)
      if (x.op === '<' || x.op === '<=' || x.op === '=') return emitCmp(x.op, x.a, x.b, true)
      const inner = printC(x)
      return inner === 'true' ? 'false' : inner === 'false' ? 'true' : `!(${inner})`
    },
    simplifyBool: true,
    onFlag: name => ctx.flags.get(name) ?? name,
    onAll: (c, printE, printC) => {
      const finite = finiteBound(c)
      if (finite) {
        const size = printE(finite)
        const vName = safeVar('$fk_', c.key)
        const prev = ctx.boundKeys.get(c.key)
        ctx.boundKeys.set(c.key, vName)
        const body = printC(c.c)
        if (prev === undefined) ctx.boundKeys.delete(c.key); else ctx.boundKeys.set(c.key, prev)
        return `((($fn: number): boolean => { if (!Number.isSafeInteger($fn) || $fn < 0) throw new RangeError('finite bound must be a natural'); for (let ${vName} = 0; ${vName} < $fn; ${vName}++) { if (!(${body})) return false } return true })(${size}))`
      }
      const names = boundOf(c)
      const ksVars = names.map((n, i) => safeVar(i === 0 ? '$qk_' : `$qk${i}_`, n))
      const keysExpr = names.length === 1 ? emitKeysExpr(c.c, c.key) : emitTupleKeysExpr(c)
      const saved = names.map(n => [n, ctx.boundKeys.get(n)] as const)
      for (let i = 0; i < names.length; i++) ctx.boundKeys.set(names[i]!, ksVars[i]!)
      const body = printC(c.c)
      let joined: string | undefined
      if (names.length === 2) {
        const j = joinOf(c.c, names[0]!, names[1]!)
        if (j) {
          const xExpr = printE(j.x), yExpr = printE(j.y)
          ctx.helpers.add('join')
          joined = `$join(${keysExpr}, (${ksVars[0]}: number) => ${xExpr}, (${ksVars[1]}: number) => ${yExpr}, (${ksVars[0]}: number, ${ksVars[1]}: number) => ${body})`
        }
      }
      for (const [n, prev] of saved) { if (prev === undefined) ctx.boundKeys.delete(n); else ctx.boundKeys.set(n, prev) }
      if (joined) return joined
      return names.length === 1
        ? `${keysExpr}.every((${ksVars[0]}: number) => ${body})`
        : `(($ks: readonly number[]): boolean => ${ksVars.map(k => `$ks.every((${k}: number) => `).join('')}${body}${')'.repeat(ksVars.length)})(${keysExpr})`
    },
  })

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
      default: return unreachable(kind)
    }
  }

  return {emitNum, emitCond, emitSignedDiff, emitBoolVal, emitChoiceVal, emitKindVal, emitBreaksExpr, emitKeysExpr}
}

// --- Direct recurrence / custom fn emitter (typed helpers live in core/codegen.ts) -----------------------------------

function emitRuleFnHelper(fnId: string, fn: Fn, helpers: Set<EmitHelper>): string[] {
  const direct = directOf(fn)
  if (direct?.kind === 'recur') return emitRecurHelper(fnId, direct, helpers)
  const arity = fn.arity ?? 1
  const params = Array.from({length: arity}, (_, i) => `a${i}: number`).join(', ')
  return [`const ${fnId} = (${fn.call ?? fn.js}) as (${params}) => number`]
}

function emitRecurHelper(fnId: string, d: Extract<DirectFn, {kind: 'recur'}>, helpers: Set<EmitHelper>): string[] {
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
    else if (ud?.kind === 'recur') lines.push(...emitRecurHelper(uid, ud, helpers))
    else lines.push(...emitRuleFnHelper(uid, ufn, helpers))
  }
  const bound = new Map<string, string>()
  const {printE: emitE} = createPrinter({
    onVar: n => bound.get(n) ?? n,
    onGet: (map, key, printE) => {
      const wd = parseWordDivisionName(map)
      if (wd) {
        const args = wordDivisionArgs(key, wd.width)
        if (!args) throw new Error(`${map}: invalid word division tuple key`)
        helpers.add('wordDiv')
        return `$wordDiv(${wd.width}, ${JSON.stringify(wd.part)}, ${wd.index}, [${args.map(printE).join(', ')}])`
      }
      const mDiv = /^(div|mod)\$(\d+)$/.exec(map)
      if (mDiv) {
        const k = Number(mDiv[2]), a = printE(key)
        return mDiv[1] === 'div' ? `Math.floor(${a} / ${k})` : `(${a} % ${k})`
      }
      const ufn = d.uses[map]!, uid = useNames.get(map)!, arity = ufn.arity ?? 1
      const args = arity > 1 ? pairedArgs(key, arity) : undefined
      return args ? `${uid}(${args.map(printE).join(', ')})` : `${uid}(${printE(key)})`
    },
    onPair: (a, b) => { helpers.add('cpair'); return `$cpair(${a}, ${b})` },
    onProj: (a, k) => { helpers.add('cunpair'); return `$cunpair(${a})[${k}]` },
    onNot: (x, printC) => `!(${printC(x)})`,
    onFlag: name => safeVar('$flag_', name),
    onAll: (c, printE, printC) => {
      const finite = finiteBound(c)
      if (finite) {
        const size = printE(finite), vName = safeVar('$rk_', c.key)
        bound.set(c.key, vName)
        const body = printC(c.c)
        bound.delete(c.key)
        return `((($fn: number): boolean => { for (let ${vName} = 0; ${vName} < $fn; ${vName}++) { if (!(${body})) return false } return true })(${size}))`
      }
      helpers.add('breaks')
      const names = boundOf(c)
      const ksVars = names.map((n, i) => safeVar(i === 0 ? '$rk_' : `$rk${i}_`, n))
      const parts = names.map(n => breaksOf(names.length > 1 ? crossFree(c.c, names) : c.c, n))
      const cmps = parts.flatMap(b => b.cmps).map(cm => `[${printE(cm.value)}, ${cm.off ? printE(cm.off) : '0'}, ${cm.minus}]`).join(', ')
      let keysExpr = `$breaks({}, [], [${cmps}])`
      if (names.length > 1) { helpers.add('spread'); keysExpr = `$spread(${keysExpr}, ${names.length})` }
      for (let i = 0; i < names.length; i++) bound.set(names[i]!, ksVars[i]!)
      const body = printC(c.c)
      for (const n of names) bound.delete(n)
      return names.length === 1
        ? `${keysExpr}.every((${ksVars[0]}: number) => ${body})`
        : `(($ks: readonly number[]): boolean => ${ksVars.map(k => `$ks.every((${k}: number) => `).join('')}${body}${')'.repeat(ksVars.length)})(${keysExpr})`
    },
  })
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

function collectFnHelpers(fns: Record<string, Fn> | undefined, helpers: Set<EmitHelper>): {fnNames: Map<string, string>, fnHelperLines: string[]} {
  const fnNames = new Map<string, string>()
  const fnHelperLines: string[] = []
  for (const [k, fn] of Object.entries(fns ?? {})) {
    if (/^(div|mod)\$\d+$/.test(k)) continue
    const d = directOf(fn)
    if (d?.kind === 'div' || d?.kind === 'mod' || d?.kind === 'const') continue
    const id = safeVar('$fn_', k)
    fnNames.set(k, id)
    fnHelperLines.push(...emitRuleFnHelper(id, fn, helpers))
  }
  return {fnNames, fnHelperLines}
}

function buildArithDesc(decPlaces: ReadonlySet<number>, roundedPlaces: ReadonlySet<number>): string {
  const placesList = [...decPlaces].sort((a, b) => a - b)
  const roundedList = [...roundedPlaces].sort((a, b) => a - b)
  if (roundedList.length > 0) {
    return `exact scaled fixed-point integers (${placesList.map(p => `10^-${p}`).join(', ')}); inputs rounded half-even to ${roundedList.map(p => `10^-${p}`).join(', ')}; laws hold for the rounded values; safe integer range <= 2^53 - 1`
  }
  if (placesList.length > 0) {
    return `exact scaled fixed-point integers (${placesList.map(p => `10^-${p}`).join(', ')}); throws RangeError on inputs exceeding ${placesList.join('/')} decimal places (matching encodeInput); safe integer range <= 2^53 - 1`
  }
  return 'exact JavaScript safe integers over N/Z (truncated natural subtraction max(0, a - b); safe range <= 2^53 - 1)'
}

// --- Header comment formatter ----------------------------------------------------------------------------------------

function renderHeader(info: {
  name: string
  kind: 'rule' | 'fun' | 'ratRule' | 'chart' | 'fold' | 'loop'
  digest: string
  arithmetic: string
  laws: readonly EmitLawReport[]
  provenance?: EmitProvenance
}): string[] {
  const label = info.kind === 'fun' ? 'Pure rule' : info.kind === 'ratRule' ? 'Rational rule' : info.kind === 'chart' ? 'Statechart' : info.kind === 'fold' ? 'Fold' : info.kind === 'loop' ? 'Loop' : 'Rule'
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

  const helpers = new Set<EmitHelper>()
  const {fnNames, fnHelperLines} = collectFnHelpers(m.fns, helpers)

  const reg = makeRegistry()
  const scaleLines: string[] = []

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
      emitFixedPrep(n, k, propAccess('params', n), helpers, scaleLines)
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
      emitFixedPrep(n, k, propAccess('args', n), helpers, scaleLines)
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
  const primFailExpr = m.primitiveFailure ? em.emitCond(m.primitiveFailure) : undefined

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

  const arithDesc = buildArithDesc(decPlaces, roundedPlaces)

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

  const helperLines = renderTypedHelpers(ctx.helpers)
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
  if (primFailExpr && primFailExpr !== 'false') bodyLines.push(`  if (${primFailExpr}) throw new RangeError(${JSON.stringify(`${meta.name}: arithmetic trap`)})`)
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

function kindVarNames(base: string, k: KindInfo): string[] {
  switch (k.kind) {
    case 'nat': case 'bool': case 'oneOf': return [base]
    case 'int': case 'decimal': return [base, `${base}$neg`]
    case 'maybe': return [`${base}$some`, ...kindVarNames(base, k.of)]
    case 'record': return k.fields.flatMap(([f, fk]) => kindVarNames(`${base}.${f}`, fk))
    case 'variant': return [base, ...k.cases.flatMap(([c, fs]) => fs.flatMap(([f, fk]) => kindVarNames(`${base}.${c}.${f}`, fk)))]
    case 'str': return [base, `${base}$len`, ...k.patterns.map((_, i) => `${base}$like${i}`)]
    case 'fixed': return Array.from({length: k.width === 8 ? 1 : k.width / 16}, (_, i) => `${base}$${i}`)
    case 'unknown': return k.vars.length ? k.vars.map(v => (v === 'x' ? base : v.startsWith('x') ? `${base}${v.slice(1)}` : v)) : [base]
    default: return unreachable(k)
  }
}

// Register map-part getters for arbitrary KindInfo values stored in a Map or readonly array.
function registerAnyCellParts(
  rawBase: string,
  kind: KindInfo,
  mapName: string,
  containerExpr: string,
  rootType: string,
  rootIsMap: boolean,
  oneBased: boolean,
  defExpr: string,
  valAccess: (rootVar: string) => string,
  guard: string | undefined,
  ctxMaps: Map<string, MapInfo>,
  cellGetters: string[],
  helpers: Set<EmitHelper>,
  mMaps: Record<string, number> | undefined,
  prefix: string,
): void {
  const mkGetter = (raw: string, retType: string, bodyExpr: string, fallback: string, fieldKind: KindInfo) => {
    const gid = safeVar(prefix, raw)
    const dynamicDef = rootIsMap && /\bstate\b/.test(defExpr)
    const lookup = rootIsMap
      ? `  const $c = m.get(k) ?? ${dynamicDef ? 'd' : defExpr}`
      : oneBased
        ? `  const $c = k >= 1 && k <= m.length ? m[k - 1] : undefined`
        : `  const $c = m[k]`
    const ret = rootIsMap
      ? (guard ? `  return (${guard}) ? ${bodyExpr} : ${fallback}` : `  return ${bodyExpr}`)
      : (guard ? `  return $c !== undefined && (${guard}) ? ${bodyExpr} : ${fallback}` : `  return $c !== undefined ? ${bodyExpr} : ${fallback}`)
    const paramType = rootIsMap ? `ReadonlyMap<number, ${rootType}>` : `readonly ${rootType}[]`
    cellGetters.push(`function ${gid}(m: ${paramType}, k: number${dynamicDef ? `, d: ${rootType}` : ''}): ${retType} {`, lookup, ret, '}')
    ctxMaps.set(raw, {
      rawName: raw,
      mapName,
      stateExpr: containerExpr,
      defaultVal: mMaps?.[raw] ?? 0,
      fieldKind,
      getterTpl: `${gid}(${containerExpr}, __K__${dynamicDef ? `, ${defExpr}` : ''})`,
    })
  }
  const vExpr = valAccess('$c')
  switch (kind.kind) {
    case 'nat': case 'unknown':
      mkGetter(rawBase, 'number', vExpr, '0', kind)
      return
    case 'bool':
      mkGetter(rawBase, 'boolean', vExpr, 'false', kind)
      return
    case 'oneOf':
      mkGetter(rawBase, kindTsType(kind), vExpr, JSON.stringify(kind.values[0]!), kind)
      return
    case 'int':
      mkGetter(rawBase, 'number', `Math.max(${vExpr}, 0)`, '0', {kind: 'nat'})
      mkGetter(`${rawBase}$neg`, 'number', `Math.max(-(${vExpr}), 0)`, '0', {kind: 'nat'})
      return
    case 'decimal': {
      const scale = 10 ** kind.places
      const sCall = kind.round === 'half-even'
        ? (helpers.add('decRound'), `$decRound(${vExpr}, ${kind.places}, ${JSON.stringify(rawBase)})`)
        : (helpers.add('dec'), `$dec(${vExpr}, ${kind.places}, ${scale}, ${JSON.stringify(rawBase)})`)
      mkGetter(rawBase, 'number', `Math.max(${sCall}, 0)`, '0', {kind: 'nat'})
      mkGetter(`${rawBase}$neg`, 'number', `Math.max(-(${sCall}), 0)`, '0', {kind: 'nat'})
      return
    }
    case 'maybe': {
      mkGetter(`${rawBase}$some`, 'boolean', `(${vExpr} !== null)`, 'false', {kind: 'bool'})
      const ig = guard ? `${guard} && ${vExpr} !== null` : `${vExpr} !== null`
      registerAnyCellParts(rawBase, kind.of, mapName, containerExpr, rootType, rootIsMap, oneBased, defExpr, valAccess, ig, ctxMaps, cellGetters, helpers, mMaps, prefix)
      return
    }
    case 'record':
      for (const [f, fk] of kind.fields) {
        registerAnyCellParts(`${rawBase}.${f}`, fk, mapName, containerExpr, rootType, rootIsMap, oneBased, defExpr, rv => propAccess(valAccess(rv), f), guard, ctxMaps, cellGetters, helpers, mMaps, prefix)
      }
      return
    case 'variant': {
      const names = kind.cases.map(([c]) => c)
      helpers.add('idx')
      mkGetter(rawBase, 'number', `$idx(${propAccess(vExpr, kind.tagKey)}, [${names.map(n => JSON.stringify(n)).join(', ')}])`, '0', {kind: 'nat'})
      for (const [c, fs] of kind.cases) {
        const cg = guard ? `${guard} && ${propAccess(vExpr, kind.tagKey)} === ${JSON.stringify(c)}` : `${propAccess(vExpr, kind.tagKey)} === ${JSON.stringify(c)}`
        for (const [f, fk] of fs) {
          registerAnyCellParts(`${rawBase}.${c}.${f}`, fk, mapName, containerExpr, rootType, rootIsMap, oneBased, defExpr, rv => propAccess(valAccess(rv), f), cg, ctxMaps, cellGetters, helpers, mMaps, prefix)
        }
      }
      return
    }
    case 'str':
      mkGetter(rawBase, 'string', vExpr, "''", kind)
      mkGetter(`${rawBase}$len`, 'number', `${vExpr}.length`, '0', {kind: 'nat'})
      kind.patterns.forEach((p, i) => {
        helpers.add('glob')
        mkGetter(`${rawBase}$like${i}`, 'boolean', `$globMatch(${JSON.stringify(p)}, ${vExpr})`, 'false', {kind: 'bool'})
      })
      return
    case 'fixed': {
      helpers.add('fixedLimbs')
      const n = kind.width === 8 ? 1 : kind.width / 16
      for (let i = 0; i < n; i++) {
        mkGetter(`${rawBase}$${i}`, 'number', `$fixedLimbs(${vExpr}, ${kind.width}, ${kind.signed}, ${JSON.stringify(rawBase)})[${i}]!`, '0', {kind: 'nat'})
      }
      return
    }
    default: return unreachable(kind)
  }
}

// Emit candidate witness search for `exists(...)` in preconditions or assumptions (matching core/dsl.ts's withSkolems).
function emitSkolemSearch(
  skolems: readonly {readonly vars: readonly string[], readonly body: C}[],
  reg: SlotRegistry,
  em: ReturnType<typeof emitTsCode>,
  lines: string[],
  tag: string,
): void {
  const collectAtoms = (c: C, bound: ReadonlySet<string>, out: {k: Record<string, number>, plus: E[], minus: E[]}[]): void => {
    switch (c.op) {
      case 'not': collectAtoms(c.x, bound, out); return
      case 'and': case 'or': for (const y of c.xs) collectAtoms(y, bound, out); return
      case 'flag': case 'all': return
      case '<': case '<=': case '=': {
        const lin = emptyLin()
        addLin(lin, c.a, 1)
        addLin(lin, c.b, -1)
        const ks: Record<string, number> = {}
        const plus: E[] = [], minus: E[] = []
        let ok = true
        for (const [n, coeff] of lin.vars) {
          if (bound.has(n)) ks[n] = (ks[n] ?? 0) + coeff
          else if (coeff > 0) minus.push(coeff === 1 ? {op: 'var', name: n} : {op: 'mul', k: coeff, a: {op: 'var', name: n}})
          else if (coeff < 0) plus.push(coeff === -1 ? {op: 'var', name: n} : {op: 'mul', k: -coeff, a: {op: 'var', name: n}})
        }
        for (const r of lin.rest) {
          if ([...JSON.stringify(r.e).matchAll(/"op":"var","name":"([^"]+)"/g)].some(m => bound.has(m[1]!))) { ok = false; break }
          if (r.coeff > 0) minus.push(r.coeff === 1 ? r.e : {op: 'mul', k: r.coeff, a: r.e})
          else if (r.coeff < 0) plus.push(r.coeff === -1 ? r.e : {op: 'mul', k: -r.coeff, a: r.e})
        }
        if (lin.constVal > 0) minus.push({op: 'const', value: lin.constVal})
        else if (lin.constVal < 0) plus.push({op: 'const', value: -lin.constVal})
        if (ok && Object.keys(ks).length > 0) out.push({k: ks, plus, minus})
        return
      }
      default: return unreachable(c)
    }
  }
  const sumTs = (es: E[]): string => es.length === 0 ? '0' : es.length === 1 ? em.emitNum(es[0]!) : `(${es.map(e => em.emitNum(e)).join(' + ')})`

  skolems.forEach((sk, idx) => {
    const groups: {pos: string, neg?: string}[] = []
    for (const vName of sk.vars) if (!vName.endsWith('$neg')) groups.push(sk.vars.includes(`${vName}$neg`) ? {pos: vName, neg: `${vName}$neg`} : {pos: vName})
    for (const vName of sk.vars) if (vName.endsWith('$neg') && !sk.vars.includes(vName.slice(0, -4))) groups.push({pos: vName})
    for (const vName of sk.vars) {
      const local = safeVar(`$sk_${tag}_`, vName)
      lines.push(`  let ${local} = 0`)
      reg.slots.set(vName, {kind: 'nat', ts: local})
    }
    const bound = new Set(sk.vars)
    const atoms: {k: Record<string, number>, plus: E[], minus: E[]}[] = []
    collectAtoms(sk.body, bound, atoms)
    const bodyExpr = em.emitCond(sk.body)
    const candExprs = groups.map((g, gi) => {
      const arr = `$skc_${tag}_${idx}_${gi}`
      const cands: string[] = ['0']
      for (const a of atoms) {
        const cp = a.k[g.pos] ?? 0
        const cn = g.neg ? (a.k[g.neg] ?? 0) : 0
        const otherKeys = Object.keys(a.k).filter(n => n !== g.pos && n !== g.neg)
        if (otherKeys.length === 0) {
          const rhs = `((${sumTs(a.plus)}) - (${sumTs(a.minus)}))`
          const coeffs = g.neg ? [...new Set([cp, -cn].filter(c => c !== 0))] : (cp !== 0 ? [cp] : [])
          for (const coeff of coeffs) {
            const qExpr = `Math.trunc(${rhs} / ${coeff})`
            cands.push(qExpr, `(${qExpr} - 1)`, `(${qExpr} + 1)`)
          }
        }
      }
      lines.push(`  const ${arr} = [${cands.join(', ')}]`)
      return {g, arr}
    })
    const okVar = `$skok_${tag}_${idx}`
    lines.push(`  let ${okVar} = false`)
    const emitLoops = (gi: number, indent: string) => {
      if (gi === candExprs.length) {
        lines.push(`${indent}if (${bodyExpr}) { ${okVar} = true; break }`)
        return
      }
      const {g, arr} = candExprs[gi]!
      const cv = `$skv_${tag}_${idx}_${gi}`
      lines.push(`${indent}for (const ${cv} of ${arr}) {`)
      if (g.neg) {
        lines.push(`${indent}  ${safeVar(`$sk_${tag}_`, g.pos)} = Math.max(${cv}, 0)`)
        lines.push(`${indent}  ${safeVar(`$sk_${tag}_`, g.neg)} = Math.max(-(${cv}), 0)`)
      } else {
        lines.push(`${indent}  if (${cv} < 0) continue`)
        lines.push(`${indent}  ${safeVar(`$sk_${tag}_`, g.pos)} = ${cv}`)
      }
      emitLoops(gi + 1, `${indent}  `)
      if (gi + 1 < candExprs.length) lines.push(`${indent}  if (${okVar}) break`)
      lines.push(`${indent}}`)
    }
    emitLoops(0, '  ')
    lines.push(`  if (!${okVar}) { ${sk.vars.map(vName => `${safeVar(`$sk_${tag}_`, vName)} = 0`).join('; ')} }`)
  })
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

  const rawM = r.machine
  const m = rawM.history ? rawM : sumRuntime(rawM)
  const recompute = recomputedSums(rawM)
  const arity = mapArities(m)
  const digest = machineDigest(rawM)
  const sumNames = Object.keys(rawM.sums ?? {}).filter(sn => !meta.state.some(([n]) => n === sn))

  const hasParams = meta.params.length > 0
  const hasInputs = meta.inputs.length > 0 || meta.carried.length > 0 || meta.seqs.length > 0 || meta.seqTables.length > 0 || meta.carriedLists.length > 0

  const decPlaces = new Set<number>()
  const roundedPlaces = new Set<number>()
  for (const [, , k] of [...meta.params, ...meta.inputs]) {
    decimalPlacesIn(k, decPlaces)
    decimalRoundedPlacesIn(k, roundedPlaces)
  }
  for (const [, k] of meta.state) { decimalPlacesIn(k, decPlaces); decimalRoundedPlacesIn(k, roundedPlaces) }
  for (const [, , k] of meta.maps) if (k) { decimalPlacesIn(k, decPlaces); decimalRoundedPlacesIn(k, roundedPlaces) }
  for (const [, k] of meta.items) { decimalPlacesIn(k, decPlaces); decimalRoundedPlacesIn(k, roundedPlaces) }
  for (const nt of meta.nodes) { decimalPlacesIn(nt.kind, decPlaces); decimalRoundedPlacesIn(nt.kind, roundedPlaces) }
  for (const cl of meta.carriedLists) { decimalPlacesIn(cl.kind, decPlaces); decimalRoundedPlacesIn(cl.kind, roundedPlaces) }

  const helpers = new Set<EmitHelper>()
  const {fnNames, fnHelperLines} = collectFnHelpers(m.fns, helpers)

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
      emitFixedPrep(n, k, propAccess('params', n), helpers, initScaleLines)
      emitFixedPrep(n, k, propAccess('params', n), helpers, stepScaleLines)
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
      emitFixedPrep(n, k, propAccess('input', n), helpers, stepScaleLines)
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
      emitFixedPrep(n, k, propAccess('state', n), helpers, stepScaleLines)
      registerKind(reg, n, k, propAccess('state', n))
    }
  }
  for (const sn of sumNames) reg.slots.set(sn, {kind: 'nat', ts: propAccess('state', sn)})

  const eachMaps = new Set<string>()
  for (const [rawMap, w] of Object.entries(m.step.maps ?? {})) if ('each' in w) eachMaps.add(rawMap)
  const cellEachMaps = new Set<string>()
  for (const [mapName, , cellKind] of meta.maps) {
    if (cellKind && kindVarNames(mapName, cellKind).some(p => eachMaps.has(p))) cellEachMaps.add(mapName)
  }

  const ctxMaps = new Map<string, MapInfo>()
  const cellGetters: string[] = []
  const cellPartMapNames = new Map<string, string[]>()

  for (const [mapName, dflt, cellKind, cellInit] of meta.maps) {
    if (!cellKind) {
      ctxMaps.set(mapName, {
        rawName: mapName,
        mapName,
        stateExpr: propAccess('state', mapName),
        defaultVal: dflt,
        fieldKind: {kind: 'nat'},
        ...(eachMaps.has(mapName) ? {dynamicDefaultExpr: propAccess('state', `${mapName}_default`)} : {}),
      })
    } else {
      const defLit = rawToTsLiteral(cellInit, cellKind)
      const defExpr = cellEachMaps.has(mapName) ? propAccess('state', `${mapName}_default`) : defLit
      const simpleRec = cellKind.kind === 'record' && cellKind.fields.every(([, fk]) => fk.kind === 'nat' || fk.kind === 'bool' || fk.kind === 'oneOf' || fk.kind === 'unknown')
      const simpleVar = cellKind.kind === 'variant' && cellKind.cases.every(([, fs]) => fs.every(([, fk]) => fk.kind === 'nat' || fk.kind === 'bool' || fk.kind === 'oneOf' || fk.kind === 'unknown'))
      if (simpleRec) {
        const parts: string[] = []
        for (const [f, fk] of cellKind.fields) {
          const raw = `${mapName}.${f}`
          parts.push(raw)
          ctxMaps.set(raw, {
            rawName: raw,
            mapName,
            stateExpr: propAccess('state', mapName),
            defaultVal: m.maps?.[raw] ?? 0,
            fieldKind: fk,
            getterTpl: `((${propAccess('state', mapName)}.get(__K__) ?? ${defExpr}).${f})`,
          })
        }
        cellPartMapNames.set(mapName, parts)
      } else if (simpleVar) {
        const parts: string[] = [mapName]
        ctxMaps.set(mapName, {
          rawName: mapName,
          mapName,
          stateExpr: propAccess('state', mapName),
          defaultVal: 0,
          fieldKind: cellKind,
          dynamicDefaultExpr: defExpr,
        })
        for (const [c, fs] of cellKind.cases) {
          for (const [f, fk] of fs) {
            const raw = `${mapName}.${c}.${f}`
            parts.push(raw)
            const gid = safeVar('$get_', raw)
            if (cellEachMaps.has(mapName)) {
              ctxMaps.set(raw, {
                rawName: raw,
                mapName,
                stateExpr: propAccess('state', mapName),
                defaultVal: m.maps?.[raw] ?? 0,
                fieldKind: fk,
                getterTpl: `${gid}(${propAccess('state', mapName)}, __K__, ${defExpr})`,
              })
              cellGetters.push(
                `function ${gid}(m: ReadonlyMap<number, ${kindTsType(cellKind)}>, k: number, d: ${kindTsType(cellKind)}): ${kindTsType(fk)} {`,
                '  const c = m.get(k) ?? d',
                `  return ${propAccess('c', cellKind.tagKey)} === ${JSON.stringify(c)} ? ${propAccess('c', f)} : ${kindDefaultTs(fk)}`,
                '}',
              )
            } else {
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
        cellPartMapNames.set(mapName, parts)
      } else {
        const before = new Set(ctxMaps.keys())
        registerAnyCellParts(mapName, cellKind, mapName, propAccess('state', mapName), kindTsType(cellKind), true, false, defExpr, rv => rv, undefined, ctxMaps, cellGetters, helpers, m.maps, '$get_')
        cellPartMapNames.set(mapName, [...ctxMaps.keys()].filter(k => !before.has(k)))
      }
    }
  }

  for (const listName of meta.lists) {
    reg.slots.set(`${listName}_len`, {kind: 'nat', ts: `${propAccess('state', listName)}.length`})
    ctxMaps.set(listName, {rawName: listName, mapName: listName, stateExpr: propAccess('state', listName), defaultVal: 0, fieldKind: {kind: 'nat'}, getterTpl: `(${propAccess('state', listName)}[__K__] ?? 0)`})
  }

  const itemPartMapNames = new Map<string, string[]>()
  for (const [itemName, itemKind] of meta.items) {
    reg.slots.set(`${itemName}_len`, {kind: 'nat', ts: `${propAccess('state', itemName)}.length`})
    const simpleRec = itemKind.kind === 'record' && itemKind.fields.every(([, fk]) => fk.kind === 'nat' || fk.kind === 'bool' || fk.kind === 'oneOf' || fk.kind === 'unknown')
    const simpleScalar = itemKind.kind === 'nat' || itemKind.kind === 'bool' || itemKind.kind === 'oneOf' || itemKind.kind === 'unknown'
    if (simpleRec) {
      const parts: string[] = []
      for (const [f, fk] of itemKind.fields) {
        const raw = `${itemName}.${f}`
        parts.push(raw)
        const gid = safeVar('$item_', raw)
        ctxMaps.set(raw, {rawName: raw, mapName: itemName, stateExpr: propAccess('state', itemName), defaultVal: 0, fieldKind: fk, getterTpl: `${gid}(${propAccess('state', itemName)}, __K__)`})
        cellGetters.push(
          `function ${gid}(xs: readonly ${kindTsType(itemKind)}[], k: number): ${kindTsType(fk)} {`,
          '  const c = xs[k]',
          `  return c !== undefined ? ${propAccess('c', f)} : ${kindDefaultTs(fk)}`,
          '}',
        )
      }
      itemPartMapNames.set(itemName, parts)
    } else if (simpleScalar) {
      const gid = safeVar('$item_', itemName)
      ctxMaps.set(itemName, {rawName: itemName, mapName: itemName, stateExpr: propAccess('state', itemName), defaultVal: 0, fieldKind: itemKind, getterTpl: `${gid}(${propAccess('state', itemName)}, __K__)`})
      cellGetters.push(
        `function ${gid}(xs: readonly ${kindTsType(itemKind)}[], k: number): ${kindTsType(itemKind)} {`,
        `  return xs[k] ?? ${kindDefaultTs(itemKind)}`,
        '}',
      )
      itemPartMapNames.set(itemName, [itemName])
    } else {
      const before = new Set(ctxMaps.keys())
      registerAnyCellParts(itemName, itemKind, itemName, propAccess('state', itemName), kindTsType(itemKind), false, false, kindDefaultTs(itemKind), rv => rv, undefined, ctxMaps, cellGetters, helpers, m.maps, '$item_')
      itemPartMapNames.set(itemName, [...ctxMaps.keys()].filter(k => !before.has(k)))
    }
  }

  const nodePartMapNames = new Map<string, string[]>()
  for (const nt of meta.nodes) {
    const nodeTs = `{ readonly value: ${kindTsType(nt.kind)}${nt.children.map(c => `; readonly ${propKey(c)}: number`).join('')} }`
    reg.slots.set(`${nt.name}_size`, {kind: 'nat', ts: `${propAccess('state', nt.name)}.length`})
    const before = new Set(ctxMaps.keys())
    registerAnyCellParts(nt.name, nt.kind, nt.name, propAccess('state', nt.name), nodeTs, false, true, `{ value: ${kindDefaultTs(nt.kind)}${nt.children.map(c => `, ${propKey(c)}: 0`).join('')} }`, rv => `${rv}.value`, undefined, ctxMaps, cellGetters, helpers, m.maps, '$node_')
    for (const c of nt.children) {
      const raw = `${nt.name}^${c}`
      const gid = safeVar('$nodec_', raw)
      cellGetters.push(`function ${gid}(xs: readonly ${nodeTs}[], k: number): number { return k >= 1 && k <= xs.length ? ${propAccess('xs[k - 1]!', c)} : 0 }`)
      ctxMaps.set(raw, {rawName: raw, mapName: nt.name, stateExpr: propAccess('state', nt.name), defaultVal: 0, fieldKind: {kind: 'nat'}, getterTpl: `${gid}(${propAccess('state', nt.name)}, __K__)`})
    }
    if (nt.folds.length) {
      const foldTs = `{ ${nt.folds.map(f => `readonly ${propKey(f.name)}: number`).join('; ')} }`
      for (const f of nt.folds) {
        const raw = `${nt.name}$${f.name}`
        const gid = safeVar('$nodef_', raw)
        cellGetters.push(`function ${gid}(xs: readonly ${foldTs}[], k: number): number { return k >= 1 && k <= xs.length ? ${propAccess('xs[k - 1]!', f.name)} : ${f.empty} }`)
        ctxMaps.set(raw, {rawName: raw, mapName: nt.name, stateExpr: propAccess('state', `_${nt.name}_folds`), defaultVal: f.empty, fieldKind: {kind: 'nat'}, getterTpl: `${gid}(${propAccess('state', `_${nt.name}_folds`)}, __K__)`})
      }
    }
    nodePartMapNames.set(nt.name, [...ctxMaps.keys()].filter(k => !before.has(k)))
  }

  // Carried inputs: maps, seqs, seqTables, carriedLists (with fold evaluation).
  const carriedPrepLines: string[] = []
  for (const cn of meta.carried) {
    const cmVar = safeVar('$cm_', cn)
    carriedPrepLines.push(
      `  const ${cmVar}: ReadonlyMap<number, number> = ${propAccess('input', cn)} instanceof Map ? ${propAccess('input', cn)} : new Map([...${propAccess('input', cn)}].map($k => [$k, 1] as const))`,
      `  for (const [$ck, $cv] of ${cmVar}) if (!Number.isSafeInteger($ck) || $ck < 0 || !Number.isSafeInteger($cv) || $cv < 0) throw new RangeError(${JSON.stringify(`${meta.name}: invalid carried map ${cn}`)})`,
    )
    ctxMaps.set(cn, {rawName: cn, mapName: cn, stateExpr: cmVar, defaultVal: 0, fieldKind: {kind: 'nat'}})
  }
  for (const sn of meta.seqs) {
    reg.slots.set(`${sn}_len`, {kind: 'nat', ts: `${propAccess('input', sn)}.length`})
    carriedPrepLines.push(`  for (const $sv of ${propAccess('input', sn)}) if (!Number.isSafeInteger($sv) || $sv < 0) throw new RangeError(${JSON.stringify(`${meta.name}: invalid sequence ${sn}`)})`)
    ctxMaps.set(sn, {rawName: sn, mapName: sn, stateExpr: propAccess('input', sn), defaultVal: 0, fieldKind: {kind: 'nat'}, getterTpl: `(${propAccess('input', sn)}[__K__] ?? 0)`})
  }
  for (const tn of meta.seqTables) {
    const cellsVar = safeVar('$stc_', tn), baseVar = safeVar('$stb_', tn), lenVar = safeVar('$stl_', tn)
    reg.slots.set(`${tn}_rows`, {kind: 'nat', ts: `${propAccess('input', tn)}.length`})
    carriedPrepLines.push(
      `  const ${cellsVar}: number[] = []`,
      `  const ${baseVar}: number[] = []`,
      `  const ${lenVar}: number[] = []`,
      `  for (const $row of ${propAccess('input', tn)}) {`,
      `    ${baseVar}.push(${cellsVar}.length)`,
      `    ${lenVar}.push($row.length)`,
      `    for (const $sv of $row) { if (!Number.isSafeInteger($sv) || $sv < 0) throw new RangeError(${JSON.stringify(`${meta.name}: invalid sequence table ${tn}`)}); ${cellsVar}.push($sv) }`,
      '  }',
    )
    ctxMaps.set(tn, {rawName: tn, mapName: tn, stateExpr: cellsVar, defaultVal: 0, fieldKind: {kind: 'nat'}, getterTpl: `(${cellsVar}[__K__] ?? 0)`})
    ctxMaps.set(`${tn}_base`, {rawName: `${tn}_base`, mapName: tn, stateExpr: baseVar, defaultVal: 0, fieldKind: {kind: 'nat'}, getterTpl: `(${baseVar}[__K__] ?? 0)`})
    ctxMaps.set(`${tn}_len`, {rawName: `${tn}_len`, mapName: tn, stateExpr: lenVar, defaultVal: 0, fieldKind: {kind: 'nat'}, getterTpl: `(${lenVar}[__K__] ?? 0)`})
  }
  const carriedListPartNames = new Map<string, string[]>()
  for (const cl of meta.carriedLists) {
    reg.slots.set(`${cl.name}_len`, {kind: 'nat', ts: `${propAccess('input', cl.name)}.length`})
    const itemChk = kindGuardChecks(cl.kind, '$clit')
    if (itemChk.length) {
      carriedPrepLines.push(`  for (const $clit of ${propAccess('input', cl.name)}) if (${itemChk.join(' || ')}) throw new RangeError(${JSON.stringify(`${meta.name}: invalid carried list ${cl.name}`)})`)
    }
    const before = new Set(ctxMaps.keys())
    registerAnyCellParts(cl.name, cl.kind, cl.name, propAccess('input', cl.name), kindTsType(cl.kind), false, false, kindDefaultTs(cl.kind), rv => rv, undefined, ctxMaps, cellGetters, helpers, undefined, '$cl_')
    carriedListPartNames.set(cl.name, [...ctxMaps.keys()].filter(k => !before.has(k)))
    for (const f of cl.folds) {
      const fVar = safeVar(`$fold_${cl.name}_`, f.name)
      ctxMaps.set(`${cl.name}$${f.name}`, {rawName: `${cl.name}$${f.name}`, mapName: cl.name, stateExpr: fVar, defaultVal: 0, fieldKind: {kind: 'nat'}, getterTpl: `(${fVar}[__K__] ?? 0)`})
    }
  }

  // Runtime derived counts (only those transitively read by step, assume, or leasts).
  const allCounts = m.counts ?? {}
  const usedCounts = new Set<string>()
  walk([m.step, m.assume ?? null, m.leasts ?? null], o => { if (o.op === 'get' && (o.map as string) in allCounts) usedCounts.add(o.map as string) })
  for (let grew = true; grew;) {
    grew = false
    for (const c of [...usedCounts]) {
      walk([allCounts[c]!.below, allCounts[c]!.body], o => {
        if (o.op === 'get' && (o.map as string) in allCounts && !usedCounts.has(o.map as string)) { usedCounts.add(o.map as string); grew = true }
      })
    }
  }
  const runtimeCounts = Object.keys(allCounts).filter(c => usedCounts.has(c))
  for (const c of runtimeCounts) {
    helpers.add('countCells')
    ctxMaps.set(c, {rawName: c, mapName: c, stateExpr: safeVar('$count_', c), defaultVal: 0, fieldKind: {kind: 'nat'}, getterTpl: `${safeVar('$count_', c)}.get(__K__)`})
  }

  // Register leasts slots before flags/assume/step so flags and step read them.
  for (const [lname, l] of Object.entries(m.leasts ?? {})) {
    reg.slots.set(lname, {kind: 'nat', ts: safeVar('$least_', lname)})
    reg.slots.set(l.some, {kind: 'nat', ts: safeVar('$leastSome_', lname)})
  }

  const ctx: EmitCtx = {reg, flags: new Map(), maps: ctxMaps, fns: m.fns ?? {}, helpers, fnNames, boundKeys: new Map(), cse: new Map()}
  const em = emitTsCode(ctx)

  const initCtx: EmitCtx = {...ctx, reg: initReg, flags: new Map(), maps: new Map(), cse: new Map()}
  const initEm = emitTsCode(initCtx)

  // Compute carried list folds (now that `em` and `initEm` exist).
  for (const cl of meta.carriedLists) {
    for (const f of cl.folds) {
      const fVar = safeVar(`$fold_${cl.name}_`, f.name)
      const foldReg = makeRegistry()
      for (const [k, s] of initReg.slots) foldReg.slots.set(k, s)
      for (const sv of initReg.signedVars) { foldReg.signedVars.add(sv); foldReg.signedTs.set(sv, initReg.signedTs.get(sv)!) }
      const itemPrep: string[] = []
      if (cl.kind.kind === 'decimal') {
        const dl = `$clf_${cl.name}_${f.name}_d`
        const call = cl.kind.round === 'half-even'
          ? (helpers.add('decRound'), `$decRound($clitem, ${cl.kind.places}, ${JSON.stringify(cl.name)})`)
          : (helpers.add('dec'), `$dec($clitem, ${cl.kind.places}, ${10 ** cl.kind.places}, ${JSON.stringify(cl.name)})`)
        itemPrep.push(`    const ${dl} = ${call}`)
        registerKind(foldReg, '$clitem', cl.kind, dl)
      } else {
        emitFixedPrep('$clitem', cl.kind, '$clitem', helpers, itemPrep)
        registerKind(foldReg, '$clitem', cl.kind, '$clitem')
      }
      foldReg.slots.set('$clacc', {kind: 'nat', ts: '$clacc'})
      const foldEm = emitTsCode({...ctx, reg: foldReg, flags: new Map(), maps: new Map(), cse: new Map()})
      const fromTs = initEm.emitNum(f.fromE)
      const stepTs = foldEm.emitNum(f.stepE)
      carriedPrepLines.push(
        `  const ${fVar}: number[] = [${fromTs}]`,
        `  for (let $fi = 0; $fi < ${propAccess('input', cl.name)}.length; $fi++) {`,
        `    const $clitem = ${propAccess('input', cl.name)}[$fi]!`,
        `    const $clacc = ${fVar}[$fi]!`,
        ...itemPrep,
        `    ${fVar}.push(${stepTs})`,
        '  }',
      )
    }
  }

  // Skolems (`exists` in pre/assume).
  const initSkolemLines: string[] = []
  const stepSkolemLines: string[] = []
  if (meta.skolems.params.length) {
    emitSkolemSearch(meta.skolems.params, initReg, initEm, initSkolemLines, 'p')
    emitSkolemSearch(meta.skolems.params, reg, em, stepSkolemLines, 'p')
  }
  if (meta.skolems.inputs.length) {
    emitSkolemSearch(meta.skolems.inputs, reg, em, stepSkolemLines, 'i')
  }

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

  // Emit runtime count declarations (using `em`, after carried prep, before leasts/flags).
  const countLines: string[] = []
  for (const c of runtimeCounts) {
    const d = allCounts[c]!
    const jVar = safeVar('$cj_', c), loVar = safeVar('$clo_', c), kVar = safeVar('$ck_', c)
    ctx.boundKeys.set(d.j, jVar)
    if (d.base && d.lo) ctx.boundKeys.set(d.lo, loVar)
    const belowTs = em.emitNum(d.below)
    ctx.boundKeys.set(d.key, kVar)
    const bodyTs = em.emitNum(d.body)
    ctx.boundKeys.delete(d.key)
    ctx.boundKeys.delete(d.j)
    if (d.lo) ctx.boundKeys.delete(d.lo)
    countLines.push(
      `  const ${safeVar('$count_', c)} = new $CountCells(($cx: number): number => {`,
      d.base && d.lo ? `    const ${jVar} = Math.floor($cx / ${d.base}), ${loVar} = $cx % ${d.base}` : `    const ${jVar} = $cx`,
      `    const $cn = ${belowTs}`,
      '    let $csum = 0',
      `    for (let ${kVar} = 0; ${kVar} < $cn; ${kVar}++) $csum += ${bodyTs}`,
      '    return $csum',
      '  })',
    )
  }

  // Emit least-key scans (before flags, since flags & step may read leasts).
  const leastLines: string[] = []
  for (const [lname, l] of Object.entries(m.leasts ?? {})) {
    helpers.add('keys')
    ctx.usesMapsView = true
    const lVar = safeVar('$least_', lname), sVar = safeVar('$leastSome_', lname)
    ctx.boundKeys.set(l.key, '$lk')
    const whereTs = em.emitCond(l.where)
    const byTs = l.by.map(b => (b.neg ? `(${em.emitNum(b.e)} - ${em.emitNum(b.neg)})` : em.emitNum(b.e)))
    ctx.boundKeys.delete(l.key)
    const ms = mapsIn({op: 'and', xs: [l.where, ...l.by.flatMap(b => [b.e, ...(b.neg ? [b.neg] : [])].map(e => ({op: '=' as const, a: e, b: e})))]})
      .filter(mp => !m.fns?.[mp] && !/^(div|mod)\$\d+$/.test(mp) && !parseWordDivisionName(mp))
    const better = l.by.map((b, i) => `$by[${i}]! !== $bb[${i}]! ? $by[${i}]! ${b.desc ? '>' : '<'} $bb[${i}]! : `).join('') + 'false'
    leastLines.push(
      `  let ${lVar} = 0, ${sVar} = 0`,
      '  {',
      `    const $lks = $keys($maps, ${JSON.stringify(ms)})`,
      '    const $lpast = $lks.pop()!',
      `    { const $lk = $lpast; if (${whereTs}) throw new RangeError(${JSON.stringify(`${meta.name}: ${lname} has no least`)}) }`,
      '    let $bk: number | undefined, $bb: readonly number[] | undefined',
      '    for (const $lk of $lks.sort((a, b) => a - b)) {',
      `      if (!(${whereTs})) continue`,
      `      const $by = [${byTs.join(', ')}]`,
      `      if ($bk === undefined || ($bb !== undefined && (${better}))) { $bk = $lk; $bb = $by }`,
      '    }',
      `    if ($bk !== undefined) { ${lVar} = $bk; ${sVar} = 1 }`,
      '  }',
    )
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
  for (const sn of sumNames) {
    if (recompute.has(sn)) continue
    const e = m.step.state?.[sn] ?? {op: 'var', name: sn}
    nextScalars.push([sn, em.emitNum(e)])
  }

  const mapUpdateLines: string[] = []
  const nextMapFields: [string, string][] = []
  const postMapExprs = new Map<string, {mapExpr: string, defExpr: string}>()

  for (const [mapName, dflt, cellKind, cellInit] of meta.maps) {
    const localMap = safeVar('next_', mapName)
    if (!cellKind) {
      const w = m.step.maps?.[mapName]
      if (!w) {
        nextMapFields.push([mapName, `new Map(${propAccess('state', mapName)})`])
        postMapExprs.set(mapName, {mapExpr: propAccess('state', mapName), defExpr: eachMaps.has(mapName) ? propAccess('state', `${mapName}_default`) : String(dflt)})
      } else if ('each' in w) {
        const localDef = safeVar('nextDef_', mapName)
        const parts = arity[mapName] ?? 1
        if (parts > 1) {
          // Tuple keys at every key (relations / multi-arity maps): exact match to core/machine.ts's writeEveryTuple.
          helpers.add('everyTuple')
          helpers.add('breaks')
          ctx.usesMapsView = true
          const ep = eachParts(w, parts)
          const eqBody: C = {op: '=', a: ep.value, b: {op: 'const', value: 0}}
          const free = crossFree(eqBody, ep.names)
          const bs = ep.names.map(nm => breaksOf(free, nm))
          const crossed = JSON.stringify(free) !== JSON.stringify(eqBody)
          let kssExpr: string
          if (crossed) {
            helpers.add('spread')
            const merged = em.emitBreaksExpr({reads: bs.flatMap(b => b.reads), cmps: bs.flatMap(b => b.cmps)})
            const mVar = safeVar('$tm_', mapName)
            mapUpdateLines.push(`  const ${mVar} = $spread(${merged}, ${parts})`)
            kssExpr = `[${Array.from({length: parts}, () => mVar).join(', ')}]`
          } else {
            kssExpr = `[${bs.map(b => em.emitBreaksExpr(b)).join(', ')}]`
          }
          for (let i = 0; i < ep.names.length; i++) ctx.boundKeys.set(ep.names[i]!, `$tx[${i}]!`)
          const valExpr = em.emitNum(ep.value)
          for (const nm of ep.names) ctx.boundKeys.delete(nm)
          const resVar = safeVar('$tw_', mapName)
          mapUpdateLines.push(
            `  const ${resVar} = $everyTuple(${kssExpr}, ${crossed}, ($tx: readonly number[]) => ${valExpr})`,
            `  const ${localMap} = ${resVar}.cells`,
            `  const ${localDef} = ${resVar}.d`,
          )
        } else if (!plainKey(w.value, w.each)) {
          helpers.add('dense')
          const ksExpr = em.emitBreaksExpr(breaksOf(w.value, w.each))
          ctx.boundKeys.set(w.each, '$k')
          const valAtK = em.emitNum(w.value)
          ctx.boundKeys.delete(w.each)
          const resVar = safeVar('$dw_', mapName)
          mapUpdateLines.push(
            `  const ${resVar} = $dense(${ksExpr}, ($k: number) => ${valAtK})`,
            `  const ${localMap} = ${resVar}.cells`,
            `  const ${localDef} = ${resVar}.d`,
          )
        } else {
          const readMaps = mapsIn(w.value).filter(mp => !m.fns?.[mp] && !/^(div|mod)\$\d+$/.test(mp) && !parseWordDivisionName(mp))
          if (readMaps.some(mp => mp !== mapName)) {
            helpers.add('every')
            helpers.add('keys')
            ctx.usesMapsView = true
            ctx.boundKeys.set(w.each, '$k')
            const valAtK = em.emitNum(w.value)
            ctx.boundKeys.delete(w.each)
            const resVar = safeVar('$ew_', mapName)
            mapUpdateLines.push(
              `  const ${resVar} = $every($keys($maps, ${JSON.stringify(readMaps)}), ($k: number) => ${valAtK})`,
              `  const ${localMap} = ${resVar}.cells`,
              `  const ${localDef} = ${resVar}.d`,
            )
          } else {
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
          }
        }
        nextMapFields.push([mapName, localMap], [`${mapName}_default`, localDef])
        postMapExprs.set(mapName, {mapExpr: localMap, defExpr: localDef})
      } else {
        const kExpr = em.emitNum(w.key)
        mapUpdateLines.push(`  const ${localMap} = new Map(${propAccess('state', mapName)})`)
        if (w.value.op === 'if' && w.value.else.op === 'get' && w.value.else.map === mapName && sameNode(w.value.else.key, w.key)) {
          mapUpdateLines.push(`  if (${em.emitCond(w.value.c)}) { ${localMap}.set(${kExpr}, ${em.emitNum(w.value.then)}) }`)
        } else {
          mapUpdateLines.push(`  ${localMap}.set(${kExpr}, ${em.emitNum(w.value)})`)
        }
        nextMapFields.push([mapName, localMap])
        postMapExprs.set(mapName, {mapExpr: localMap, defExpr: String(dflt)})
      }
    } else {
      const allParts = kindVarNames(mapName, cellKind)
      const partWrites = allParts.map(p => [p, m.step.maps?.[p]] as const).filter((e): e is readonly [string, NonNullable<typeof e[1]>] => e[1] !== undefined)
      if (!partWrites.length) {
        nextMapFields.push([mapName, `new Map(${propAccess('state', mapName)})`])
        if (cellEachMaps.has(mapName)) nextMapFields.push([`${mapName}_default`, propAccess('state', `${mapName}_default`)])
      } else {
        const firstW = partWrites[0]![1]
        if ('each' in firstW) {
          const localDef = safeVar('nextDef_', mapName)
          const eachWrites = partWrites.filter((e): e is readonly [string, {each: string, value: E}] => 'each' in e[1])
          const allPlain = eachWrites.every(([, pw]) => plainKey(pw.value, pw.each))
          let ksExpr: string
          if (allPlain) {
            helpers.add('every')
            helpers.add('keys')
            ctx.usesMapsView = true
            const readMaps = [...new Set(eachWrites.flatMap(([, pw]) => mapsIn(pw.value)).filter(mp => !m.fns?.[mp] && !/^(div|mod)\$\d+$/.test(mp) && !parseWordDivisionName(mp)))]
            ksExpr = `$keys($maps, ${JSON.stringify(readMaps)})`
          } else {
            helpers.add('dense')
            const mergedBreaks: Breaks = {
              reads: eachWrites.flatMap(([, pw]) => breaksOf(pw.value, pw.each).reads),
              cmps: eachWrites.flatMap(([, pw]) => breaksOf(pw.value, pw.each).cmps),
            }
            ksExpr = em.emitBreaksExpr(mergedBreaks)
          }
          const boundNames: string[] = []
          for (const [, pw] of eachWrites) { ctx.boundKeys.set(pw.each, '$k'); boundNames.push(pw.each) }
          const cellVal = em.emitKindVal(cellKind, mapName, part => {
            const pw = m.step.maps?.[part]
            return pw && 'each' in pw ? pw.value : {op: 'get', map: part, key: {op: 'var', name: firstW.each}}
          })
          const finalCellVal = cellKind.kind === 'decimal' ? `(${cellVal}) / ${10 ** cellKind.places}` : cellVal
          for (const bn of boundNames) ctx.boundKeys.delete(bn)
          const eqFn = `($a: ${kindTsType(cellKind)}, $b: ${kindTsType(cellKind)}) => ${emitCellEq(cellKind, '$a', '$b')}`
          const resVar = safeVar('$cw_', mapName)
          mapUpdateLines.push(
            `  const ${resVar} = ${allPlain ? '$every' : '$dense'}(${ksExpr}, ($k: number): ${kindTsType(cellKind)} => (${finalCellVal}), ${eqFn})`,
            `  const ${localMap} = ${resVar}.cells`,
            `  const ${localDef} = ${resVar}.d`,
          )
          nextMapFields.push([mapName, localMap], [`${mapName}_default`, localDef])
        } else {
          const kExpr = em.emitNum(firstW.key)
          const cellVal = em.emitKindVal(cellKind, mapName, part => {
            const pw = m.step.maps?.[part]
            return pw && 'key' in pw ? pw.value : {op: 'get', map: part, key: firstW.key}
          })
          const finalCellVal = cellKind.kind === 'decimal' ? `(${cellVal}) / ${10 ** cellKind.places}` : cellVal
          mapUpdateLines.push(`  const ${localMap} = new Map(${propAccess('state', mapName)})`, `  ${localMap}.set(${kExpr}, ${finalCellVal})`)
          nextMapFields.push([mapName, localMap])
          if (cellEachMaps.has(mapName)) nextMapFields.push([`${mapName}_default`, propAccess('state', `${mapName}_default`)])
        }
      }
      const defLit = rawToTsLiteral(cellInit, cellKind)
      for (const p of cellPartMapNames.get(mapName) ?? []) {
        postMapExprs.set(p, {mapExpr: localMap, defExpr: cellEachMaps.has(mapName) ? safeVar('nextDef_', mapName) : defLit})
      }
    }
  }

  // Plain lists (`.lists(...)`) and typed item lists (`.items(...)`).
  const itemUpdateLines: string[] = []
  const nextItemFields: [string, string][] = []
  for (const listName of meta.lists) {
    const localList = safeVar('next_', listName)
    const lenE = m.step.state?.[`${listName}_len`] ?? {op: 'var', name: `${listName}_len`}
    const nextLenExpr = em.emitNum(lenE)
    const w = m.step.maps?.[listName]
    if (w && 'each' in w) {
      ctx.boundKeys.set(w.each, '$k')
      const valExpr = em.emitNum(w.value)
      ctx.boundKeys.delete(w.each)
      itemUpdateLines.push(
        `  const $len_${listName} = ${nextLenExpr}`,
        `  const ${localList}: number[] = []`,
        `  for (let $k = 0; $k < $len_${listName}; $k++) { ${localList}.push(${valExpr}) }`,
      )
    } else if (w && 'key' in w) {
      const kExpr = em.emitNum(w.key), valExpr = em.emitNum(w.value)
      itemUpdateLines.push(
        `  const ${localList} = [...${propAccess('state', listName)}]`,
        `  const $len_${listName} = ${nextLenExpr}`,
        `  const $idx_${listName} = ${kExpr}`,
        `  if ($len_${listName} > ${localList}.length) { ${localList}.push(${valExpr}) }`,
        `  else if ($len_${listName} < ${localList}.length) { ${localList}.length = $len_${listName} }`,
        `  else if ($idx_${listName} < ${localList}.length) { ${localList}[$idx_${listName}] = ${valExpr} }`,
      )
    } else {
      itemUpdateLines.push(`  const ${localList} = [...${propAccess('state', listName)}]`, `  ${localList}.length = ${nextLenExpr}`)
    }
    nextItemFields.push([listName, localList])
  }

  for (const [itemName, itemKind] of meta.items) {
    const localList = safeVar('next_', itemName)
    const lenE = m.step.state?.[`${itemName}_len`] ?? {op: 'var', name: `${itemName}_len`}
    const nextLenExpr = em.emitNum(lenE)
    const partNames = kindVarNames(itemName, itemKind)
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
      const finalVal = itemKind.kind === 'decimal' ? `(${valExpr}) / ${10 ** itemKind.places}` : valExpr
      for (const bn of boundNames) ctx.boundKeys.delete(bn)
      itemUpdateLines.push(
        `  const $len_${itemName} = ${nextLenExpr}`,
        `  const ${localList}: ${kindTsType(itemKind)}[] = []`,
        `  for (let $k = 0; $k < $len_${itemName}; $k++) { ${localList}.push(${finalVal}) }`,
      )
    } else if (firstW && 'key' in firstW) {
      itemUpdateLines.push(`  const ${localList} = [...${propAccess('state', itemName)}]`)
      const kExpr = em.emitNum(firstW.key)
      const valExpr = em.emitKindVal(itemKind, itemName, part => {
        const pw = m.step.maps?.[part]
        return pw && 'key' in pw ? pw.value : {op: 'get', map: part, key: firstW.key}
      })
      const finalVal = itemKind.kind === 'decimal' ? `(${valExpr}) / ${10 ** itemKind.places}` : valExpr
      itemUpdateLines.push(
        `  const $len_${itemName} = ${nextLenExpr}`,
        `  const $idx_${itemName} = ${kExpr}`,
        `  if ($len_${itemName} > ${localList}.length) { ${localList}.push(${finalVal}) }`,
        `  else if ($len_${itemName} < ${localList}.length) { ${localList}.length = $len_${itemName} }`,
        `  else if ($idx_${itemName} < ${localList}.length) { ${localList}[$idx_${itemName}] = ${finalVal} }`,
      )
    } else {
      itemUpdateLines.push(`  const ${localList} = [...${propAccess('state', itemName)}]`, `  ${localList}.length = ${nextLenExpr}`)
    }
    nextItemFields.push([itemName, localList])
  }

  // Node tables (`.nodes(...)`).
  const nodeUpdateLines: string[] = []
  const nextNodeFields: [string, string][] = []
  for (const nt of meta.nodes) {
    const localNodes = safeVar('next_', nt.name)
    const localFolds = safeVar('next__folds_', nt.name)
    const sizeE = m.step.state?.[`${nt.name}_size`] ?? {op: 'var', name: `${nt.name}_size`}
    const nextSizeExpr = em.emitNum(sizeE)
    const valExpr = em.emitKindVal(nt.kind, nt.name, part => {
      const pw = m.step.maps?.[part]
      return pw && 'key' in pw ? pw.value : {op: 'const', value: 0}
    })
    const finalVal = nt.kind.kind === 'decimal' ? `(${valExpr}) / ${10 ** nt.kind.places}` : valExpr
    const childEntries = nt.children.map(c => {
      const pw = m.step.maps?.[`${nt.name}^${c}`]
      return `${propKey(c)}: ${pw && 'key' in pw ? em.emitNum(pw.value) : '0'}`
    })
    nodeUpdateLines.push(
      `  const $nsize_${nt.name} = ${nextSizeExpr}`,
      `  const ${localNodes} = [...${propAccess('state', nt.name)}]`,
    )
    if (nt.folds.length) nodeUpdateLines.push(`  const ${localFolds} = [...${propAccess('state', `_${nt.name}_folds`)}]`)
    nodeUpdateLines.push(`  if ($nsize_${nt.name} > ${localNodes}.length) {`)
    nodeUpdateLines.push(`    ${localNodes}.push({ value: ${finalVal}${childEntries.length ? `, ${childEntries.join(', ')}` : ''} })`)
    if (nt.folds.length) {
      const foldEntries = nt.folds.map(f => {
        const pw = m.step.maps?.[`${nt.name}$${f.name}`]
        return `${propKey(f.name)}: ${pw && 'key' in pw ? em.emitNum(pw.value) : String(f.empty)}`
      })
      nodeUpdateLines.push(`    ${localFolds}.push({ ${foldEntries.join(', ')} })`)
    }
    nodeUpdateLines.push('  }')
    nextNodeFields.push([nt.name, localNodes])
    if (nt.folds.length) nextNodeFields.push([`_${nt.name}_folds`, localFolds])
  }

  // Recomputed exact map sums (when a summed map uses `each`).
  const recomputeSumLines: string[] = []
  for (const sn of recompute) {
    const sum = rawM.sums![sn]!, read = mapsIn(sum.term)
    const postMaps = new Map<string, MapInfo>()
    const dfltMaps = new Map<string, MapInfo>()
    for (const mp of read) {
      const pm = postMapExprs.get(mp)
      const orig = ctxMaps.get(mp)
      if (pm && orig && !orig.getterTpl) {
        postMaps.set(mp, {...orig, stateExpr: pm.mapExpr, dynamicDefaultExpr: pm.defExpr})
        dfltMaps.set(mp, {...orig, getterTpl: pm.defExpr})
      } else if (orig) {
        const postGetter = orig.getterTpl ? orig.getterTpl.replaceAll(orig.stateExpr, safeVar('next_', orig.mapName)) : undefined
        postMaps.set(mp, {...orig, stateExpr: safeVar('next_', orig.mapName), ...(postGetter ? {getterTpl: postGetter} : {})})
        dfltMaps.set(mp, {...orig, getterTpl: orig.getterTpl ? orig.getterTpl.replaceAll(orig.stateExpr, 'new Map()') : String(orig.defaultVal)})
      }
    }
    const postEm = emitTsCode({...ctx, maps: postMaps, boundKeys: new Map([[sum.key, '$sk']]), cse: new Map()})
    const dfltEm = emitTsCode({...ctx, maps: dfltMaps, boundKeys: new Map([[sum.key, '0']]), cse: new Map()})
    const dfltTs = dfltEm.emitNum(sum.term)
    const atKeyTs = postEm.emitNum(sum.term)
    const localSum = safeVar('next_', sn)
    const errMsg = JSON.stringify(`${meta.name}: the sum ${sn} is infinite`)
    recomputeSumLines.push(`  let ${localSum} = 0`, '  {', `    const $sd = ${dfltTs}`, `    if ($sd !== 0) throw new RangeError(${errMsg})`)
    if (read.length === 1) {
      const mapVar = postMapExprs.get(read[0]!)?.mapExpr ?? safeVar('next_', ctxMaps.get(read[0]!)?.mapName ?? read[0]!)
      recomputeSumLines.push(`    for (const $sk of ${mapVar}.keys()) ${localSum} += ${atKeyTs}`)
    } else if (read.length > 1) {
      recomputeSumLines.push('    const $sks = new Set<number>()')
      for (const mp of read) {
        const mapVar = postMapExprs.get(mp)?.mapExpr ?? safeVar('next_', ctxMaps.get(mp)?.mapName ?? mp)
        recomputeSumLines.push(`    for (const $sk of ${mapVar}.keys()) $sks.add($sk)`)
      }
      recomputeSumLines.push(`    for (const $sk of $sks) ${localSum} += ${atKeyTs}`)
    }
    recomputeSumLines.push('  }')
  }

  // Build `$maps` view ONLY when `$keys` / `$breaks` / leasts / quantifiers actually need it.
  const mapsViewLines: string[] = []
  if (ctx.usesMapsView) {
    const entries: string[] = []
    for (const [mapName, , cellKind] of meta.maps) {
      if (!cellKind) {
        entries.push(`${JSON.stringify(mapName)}: ${propAccess('state', mapName)}`)
      } else {
        for (const p of cellPartMapNames.get(mapName) ?? []) entries.push(`${JSON.stringify(p)}: ${propAccess('state', mapName)}`)
      }
    }
    for (const listName of meta.lists) {
      entries.push(`${JSON.stringify(listName)}: new Map(${propAccess('state', listName)}.map(($v, $i) => [$i, $v] as const))`)
    }
    for (const [itemName] of meta.items) {
      const mv = safeVar('$iv_', itemName)
      mapsViewLines.push(`  const ${mv} = new Map(${propAccess('state', itemName)}.map((_, $i) => [$i, 1] as const))`)
      for (const p of itemPartMapNames.get(itemName) ?? []) entries.push(`${JSON.stringify(p)}: ${mv}`)
    }
    for (const nt of meta.nodes) {
      const mv = safeVar('$nv_', nt.name)
      mapsViewLines.push(`  const ${mv} = new Map(${propAccess('state', nt.name)}.map((_, $i) => [$i + 1, 1] as const))`)
      for (const p of nodePartMapNames.get(nt.name) ?? []) entries.push(`${JSON.stringify(p)}: ${mv}`)
    }
    for (const cn of meta.carried) entries.push(`${JSON.stringify(cn)}: ${safeVar('$cm_', cn)}`)
    for (const sn of meta.seqs) {
      entries.push(`${JSON.stringify(sn)}: new Map(${propAccess('input', sn)}.flatMap(($v, $i) => $v !== 0 ? [[$i, $v] as const] : []))`)
    }
    for (const tn of meta.seqTables) {
      entries.push(
        `${JSON.stringify(tn)}: new Map(${safeVar('$stc_', tn)}.flatMap(($v, $i) => $v !== 0 ? [[$i, $v] as const] : []))`,
        `${JSON.stringify(`${tn}_base`)}: new Map(${safeVar('$stb_', tn)}.flatMap(($v, $i) => $v !== 0 ? [[$i, $v] as const] : []))`,
        `${JSON.stringify(`${tn}_len`)}: new Map(${safeVar('$stl_', tn)}.flatMap(($v, $i) => $v !== 0 ? [[$i, $v] as const] : []))`,
      )
    }
    for (const cl of meta.carriedLists) {
      const mv = safeVar('$clv_', cl.name)
      mapsViewLines.push(`  const ${mv} = new Map(${propAccess('input', cl.name)}.map((_, $i) => [$i, 1] as const))`)
      for (const p of carriedListPartNames.get(cl.name) ?? []) entries.push(`${JSON.stringify(p)}: ${mv}`)
      for (const f of cl.folds) {
        entries.push(`${JSON.stringify(`${cl.name}$${f.name}`)}: new Map(${safeVar(`$fold_${cl.name}_`, f.name)}.flatMap(($v, $i) => $v !== 0 ? [[$i, $v] as const] : []))`)
      }
    }
    mapsViewLines.push(`  const $maps: Record<string, ReadonlyMap<number, unknown>> = { ${entries.join(', ')} }`)
    for (const c of runtimeCounts) mapsViewLines.push(`  $maps[${JSON.stringify(c)}] = ${safeVar('$count_', c)}`)
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

  const arithDesc = buildArithDesc(decPlaces, roundedPlaces)

  const lines: string[] = [
    ...renderHeader({name: meta.name, kind, digest, arithmetic: arithDesc, laws: reports, ...(opts.provenance ? {provenance: opts.provenance} : {})}),
    '',
  ]

  lines.push(hasParams ? `export type Params = {\n${meta.params.map(([n, , k]) => `  readonly ${propKey(n)}: ${kindTsType(k)}`).join('\n')}\n}` : 'export type Params = Record<string, never>', '')

  const inputTypeFields: string[] = [
    ...meta.inputs.map(([n, , k]) => `  readonly ${propKey(n)}: ${kindTsType(k)}`),
    ...meta.carried.map(n => `  readonly ${propKey(n)}: ReadonlyMap<number, number> | ReadonlySet<number> | readonly number[]`),
    ...meta.seqs.map(n => `  readonly ${propKey(n)}: readonly number[]`),
    ...meta.seqTables.map(n => `  readonly ${propKey(n)}: readonly (readonly number[])[]`),
    ...meta.carriedLists.map(cl => `  readonly ${propKey(cl.name)}: readonly ${kindTsType(cl.kind)}[]`),
  ]
  lines.push(hasInputs ? `export type Input = {\n${inputTypeFields.join('\n')}\n}` : 'export type Input = Record<string, never>', '')

  if (historyFields) {
    lines.push('export type HistoryRecord = {')
    for (const rf of historyFields.recordFields) {
      const k = meta.inputs.find(([n]) => n === rf)?.[2] ?? {kind: 'nat' as const}
      lines.push(`  readonly ${propKey(rf)}: ${kindTsType(k)}`)
    }
    lines.push('}', '')
  }

  const stateTypeFields: string[] = []
  for (const [n, k] of meta.state) stateTypeFields.push(`  readonly ${propKey(n)}: ${kindTsType(k)}`)
  for (const sn of sumNames) stateTypeFields.push(`  readonly ${propKey(sn)}: number`)
  for (const [mapName, , cellKind] of meta.maps) {
    stateTypeFields.push(`  readonly ${propKey(mapName)}: Map<number, ${cellKind ? kindTsType(cellKind) : 'number'}>`)
    if (!cellKind && eachMaps.has(mapName)) stateTypeFields.push(`  readonly ${propKey(`${mapName}_default`)}: number`)
    if (cellKind && cellEachMaps.has(mapName)) stateTypeFields.push(`  readonly ${propKey(`${mapName}_default`)}: ${kindTsType(cellKind)}`)
  }
  for (const listName of meta.lists) stateTypeFields.push(`  readonly ${propKey(listName)}: readonly number[]`)
  for (const [itemName, itemKind] of meta.items) stateTypeFields.push(`  readonly ${propKey(itemName)}: readonly ${kindTsType(itemKind)}[]`)
  for (const nt of meta.nodes) {
    const nodeTs = `{ readonly value: ${kindTsType(nt.kind)}${nt.children.map(c => `; readonly ${propKey(c)}: number`).join('')} }`
    stateTypeFields.push(`  readonly ${propKey(nt.name)}: readonly ${nodeTs}[]`)
    if (nt.folds.length) {
      const foldTs = `{ ${nt.folds.map(f => `readonly ${propKey(f.name)}: number`).join('; ')} }`
      stateTypeFields.push(`  readonly ${propKey(`_${nt.name}_folds`)}: readonly ${foldTs}[]`)
    }
  }
  if (historyFields) {
    for (const [sName] of historyFields.sums) {
      if (!meta.state.some(([n]) => n === sName)) stateTypeFields.push(`  readonly ${propKey(sName)}: number`)
    }
    stateTypeFields.push('  readonly _history: readonly HistoryRecord[]')
    if (historyFields.prune) stateTypeFields.push('  readonly _last: number')
  }
  lines.push(stateTypeFields.length ? `export type State = {\n${stateTypeFields.join('\n')}\n}` : 'export type State = Record<string, never>', '')

  const helperLines = renderTypedHelpers(ctx.helpers)
  if (helperLines.length) lines.push(...helperLines, '')
  if (fnHelperLines.length) lines.push(...fnHelperLines, '')
  if (cellGetters.length) lines.push(...cellGetters, '')

  // init(params)
  const initBodyLines: string[] = []
  if (paramChecks.length) initBodyLines.push(`  if (${paramChecks.join(' || ')}) throw new RangeError(${JSON.stringify(`${meta.name}: invalid params`)})`)
  initBodyLines.push(...initScaleLines, ...initSkolemLines)
  if (preExpr !== 'true') initBodyLines.push(`  if (!(${preExpr})) throw new RangeError(${JSON.stringify(`${meta.name}: params violate precondition`)})`)
  const initReturnFields: string[] = []
  for (const [n, k] of meta.state) {
    const rawInit = initEm.emitKindVal(k, n, part => m.state[part] ?? {op: 'const', value: 0})
    const initVal = k.kind === 'decimal' ? `(${rawInit}) / ${10 ** k.places}` : rawInit
    initReturnFields.push(`    ${propKey(n)}: ${initVal},`)
  }
  for (const sn of sumNames) initReturnFields.push(`    ${propKey(sn)}: 0,`)
  for (const [mapName, dflt, cellKind, cellInit] of meta.maps) {
    initReturnFields.push(`    ${propKey(mapName)}: new Map(),`)
    if (!cellKind && eachMaps.has(mapName)) initReturnFields.push(`    ${propKey(`${mapName}_default`)}: ${dflt},`)
    if (cellKind && cellEachMaps.has(mapName)) initReturnFields.push(`    ${propKey(`${mapName}_default`)}: ${rawToTsLiteral(cellInit, cellKind)},`)
  }
  for (const listName of meta.lists) initReturnFields.push(`    ${propKey(listName)}: [],`)
  for (const [itemName, itemKind] of meta.items) {
    const initLenE = m.state[`${itemName}_len`]
    if (initLenE && !(initLenE.op === 'const' && initLenE.value === 0)) {
      initReturnFields.push(`    ${propKey(itemName)}: Array.from({ length: ${initEm.emitNum(initLenE)} }, () => ${kindDefaultTs(itemKind)}),`)
    } else {
      initReturnFields.push(`    ${propKey(itemName)}: [],`)
    }
  }
  for (const nt of meta.nodes) {
    initReturnFields.push(`    ${propKey(nt.name)}: [],`)
    if (nt.folds.length) initReturnFields.push(`    ${propKey(`_${nt.name}_folds`)}: [],`)
  }
  if (historyFields) {
    for (const [sName] of historyFields.sums) {
      if (!meta.state.some(([n]) => n === sName)) initReturnFields.push(`    ${propKey(sName)}: 0,`)
    }
    initReturnFields.push('    _history: [],')
    if (historyFields.prune) initReturnFields.push('    _last: 0,')
  }
  if (initReturnFields.length) initBodyLines.push('  return {', ...initReturnFields, '  }')
  else initBodyLines.push('  return {}')
  const initUsesP = initBodyLines.some(l => /\bparams\b/.test(l))
  lines.push(`export function init(${hasParams ? (initUsesP ? 'params: Params' : '_params: Params') : '_params: Params = {}'}): State {`, ...initBodyLines, '}', '')

  // step(params, state, input)
  const stepBodyLines: string[] = []
  if (inputChecks.length) stepBodyLines.push(`  if (${inputChecks.join(' || ')}) throw new RangeError(${JSON.stringify(`${meta.name}: invalid input`)})`)
  stepBodyLines.push(...stepScaleLines, ...carriedPrepLines, ...stepSkolemLines, ...countLines, ...mapsViewLines, ...historyLines, ...leastLines, ...flagLines)
  if (assumeExpr !== 'true') stepBodyLines.push(`  if (!(${assumeExpr})) throw new RangeError(${JSON.stringify(`${meta.name}: input violates assumption`)})`)
  if (primFailExpr && primFailExpr !== 'false') stepBodyLines.push(`  if (${primFailExpr}) throw new RangeError(${JSON.stringify(`${meta.name}: arithmetic trap`)})`)
  for (const [n, expr] of nextScalars) stepBodyLines.push(`  const ${safeVar('next_', n)} = ${expr}`)
  stepBodyLines.push(...mapUpdateLines, ...itemUpdateLines, ...nodeUpdateLines, ...recomputeSumLines)

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

  const stepReturnFields: string[] = [
    ...meta.state.map(([n]) => `    ${propKey(n)}: ${safeVar('next_', n)},`),
    ...sumNames.map(sn => `    ${propKey(sn)}: ${safeVar('next_', sn)},`),
    ...nextMapFields.map(([n, expr]) => `    ${propKey(n)}: ${expr},`),
    ...nextItemFields.map(([n, expr]) => `    ${propKey(n)}: ${expr},`),
    ...nextNodeFields.map(([n, expr]) => `    ${propKey(n)}: ${expr},`),
    ...nextHistoryFields.map(([n, expr]) => `    ${propKey(n)}: ${expr},`),
  ]
  if (stepReturnFields.length) stepBodyLines.push('  return {', ...stepReturnFields, '  }')
  else stepBodyLines.push('  return {}')

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

  const makeQPrinter = (scope: 'init' | 'step') => createQPrinter({
    onVar: name => varTs(name, scope),
    add: (a, b) => `$add(${a}, ${b})`,
    sub: (a, b) => `$sub(${a}, ${b})`,
    mul: (kLit, a) => `$mul(${kLit}, ${a})`,
    min: (a, b) => `$min(${a}, ${b})`,
    max: (a, b) => `$max(${a}, ${b})`,
    cmp: (a, b) => `$cmp(${a}, ${b})`,
    onNot: inner => `!(${inner})`,
  })
  const initQ = makeQPrinter('init'), stepQ = makeQPrinter('step')

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
  const preCheck = m.pre ? initQ.printQC(m.pre) : undefined
  if (preCheck) initBody.push(`  if (!(${preCheck})) throw new RangeError(${JSON.stringify(`${meta.name}: params violate precondition`)})`)
  initBody.push('  return {')
  for (const s of meta.state) initBody.push(`    ${propKey(s)}: ${initQ.printQE(m.state[s]!)},`)
  initBody.push('  }')
  const initSig = hasParams ? (initBody.some(l => /\bparams\b/.test(l)) ? 'params: Params' : '_params: Params') : '_params: Params = {}'
  lines.push(`export function init(${initSig}): State {`, ...initBody, '}', '')

  // allowed
  const allowExpr = m.assume ? stepQ.printQC(m.assume) : 'true'
  const allowP = /\bparams\b/.test(allowExpr) ? 'params: Params' : '_params: Params'
  const allowS = /\bstate\b/.test(allowExpr) ? 'state: State' : '_state: State'
  const allowI = /\binput\b/.test(allowExpr) ? 'input: Input' : '_input: Input'
  lines.push(`export function allowed(${allowP}, ${allowS}, ${allowI}): boolean {`, `  return ${allowExpr}`, '}', '')

  // step
  const stepBody: string[] = []
  const stateFields = meta.state.map(s => `    ${propKey(s)}: ${m.step[s] ? stepQ.printQE(m.step[s]!) : propAccess('state', s)},`)
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

// --- emitFold (binary FoldRule and RoseFold) -------------------------------------------------------------------------

export function emitFold(f: AnyFold, opts: EmitFoldOptions = {}): EmitResult {
  const meta = inspectFoldMeta(f)
  const laws: Law[] = opts.laws !== undefined ? [...opts.laws] : [...meta.ownedLaws]
  const digest = foldDigest(meta.fold)
  const reports: EmitLawReport[] = []
  let allProven = laws.length > 0
  let failedVerdict: Verdict | undefined

  if (allProven) {
    const v = proveFold(f, laws)
    const ok = v.proven && v.checked
    if (!ok) { allProven = false; failedVerdict = v }
    for (const l of laws) {
      reports.push({name: l.name, kind: 'law', proven: ok, checked: ok && v.checked, ...(!ok && v.goal ? {goal: v.goal} : {}), ...(!ok && v.why ? {why: v.why} : {})})
    }
  }
  if (!allProven && !opts.allowUnproven) {
    throw new Unproven(
      laws.length === 0 ? `${meta.name}: no laws provided to prove` : `${meta.name}: not all fold laws are proven`,
      failedVerdict ?? {proven: false, checked: false, why: laws.length === 0 ? 'no laws provided' : 'unproven fold law'},
    )
  }

  const fnName = toCamel(opts.name ?? meta.name)
  const hasParams = meta.params.length > 0
  const hasInputs = meta.inputs.length > 0
  const decPlaces = new Set<number>()
  const roundedPlaces = new Set<number>()
  for (const [, , k] of [...meta.params, ...meta.inputs]) {
    decimalPlacesIn(k, decPlaces)
    decimalRoundedPlacesIn(k, roundedPlaces)
  }

  const helpers = new Set<EmitHelper>()
  const paramScaleLines: string[] = []
  const inputScaleLines: string[] = []
  const pReg = makeRegistry()
  const reg = makeRegistry()
  for (const [n, , k] of meta.params) {
    if (k.kind === 'decimal') {
      const local = safeVar('$p_', n)
      const call = k.round === 'half-even'
        ? (helpers.add('decRound'), `$decRound(${propAccess('params', n)}, ${k.places}, ${JSON.stringify(n)})`)
        : (helpers.add('dec'), `$dec(${propAccess('params', n)}, ${k.places}, ${10 ** k.places}, ${JSON.stringify(n)})`)
      paramScaleLines.push(`  const ${local} = ${call}`)
      registerKind(pReg, n, k, local)
      registerKind(reg, n, k, local)
    } else {
      emitFixedPrep(n, k, propAccess('params', n), helpers, paramScaleLines)
      registerKind(pReg, n, k, propAccess('params', n))
      registerKind(reg, n, k, propAccess('params', n))
    }
  }
  for (const [n, , k] of meta.inputs) {
    if (k.kind === 'decimal') {
      const local = safeVar('$i_', n)
      const call = k.round === 'half-even'
        ? (helpers.add('decRound'), `$decRound(${propAccess('$own', n)}, ${k.places}, ${JSON.stringify(n)})`)
        : (helpers.add('dec'), `$dec(${propAccess('$own', n)}, ${k.places}, ${10 ** k.places}, ${JSON.stringify(n)})`)
      inputScaleLines.push(`    const ${local} = ${call}`)
      registerKind(reg, n, k, local)
    } else {
      const tmp: string[] = []
      emitFixedPrep(n, k, propAccess('$own', n), helpers, tmp)
      for (const l of tmp) inputScaleLines.push(`  ${l}`)
      registerKind(reg, n, k, propAccess('$own', n))
    }
  }
  for (const outName of meta.outputs) {
    reg.slots.set(`l_${outName}`, {kind: 'nat', ts: propAccess('$l', outName)})
    reg.slots.set(`r_${outName}`, {kind: 'nat', ts: propAccess('$r', outName)})
    reg.slots.set(`$kid_${outName}`, {kind: 'nat', ts: propAccess('$kid', outName)})
  }
  if (meta.rose && meta.roseStart) {
    for (const aName of Object.keys(meta.roseStart)) {
      reg.slots.set(`$acc_${aName}`, {kind: 'nat', ts: safeVar('$acc_', aName)})
    }
  }

  const pEm = emitTsCode({reg: pReg, flags: new Map(), maps: new Map(), fns: {}, helpers, fnNames: new Map(), boundKeys: new Map(), cse: new Map()})
  const em = emitTsCode({reg, flags: new Map(), maps: new Map(), fns: {}, helpers, fnNames: new Map(), boundKeys: new Map(), cse: new Map()})

  const paramChecks = meta.params.flatMap(([n, , k]) => kindGuardChecks(k, propAccess('params', n)))
  const inputChecks = meta.inputs.flatMap(([n, , k]) => kindGuardChecks(k, propAccess('$own', n)))
  const preExpr = meta.fold.pre ? pEm.emitCond(meta.fold.pre) : 'true'
  // For rose folds, `meta.fold.assume` includes `role$ = 0` checks; bind `role$` to 0 for real nodes.
  reg.slots.set('role$', {kind: 'nat', ts: '0'})
  const assumeExpr = meta.fold.assume ? em.emitCond(meta.fold.assume) : 'true'

  const goLines: string[] = [
    '  const $go = ($t: Tree): Result => {',
    "    const $own = 'leaf' in $t ? $t.leaf : $t.node",
  ]
  if (inputChecks.length) goLines.push(`    if (${inputChecks.join(' || ')}) throw new RangeError(${JSON.stringify(`${meta.name}: invalid input`)})`)
  goLines.push(...inputScaleLines)
  if (assumeExpr !== 'true') goLines.push(`    if (!(${assumeExpr})) throw new RangeError(${JSON.stringify(`${meta.name}: input violates assumption`)})`)
  const leafSrc = meta.rose ? meta.roseLeaf! : meta.fold.leaf
  const leafObj = `{ ${meta.outputs.map(n => `${propKey(n)}: ${em.emitNum(leafSrc[n]!)}`).join(', ')} }`
  goLines.push(`    if ('leaf' in $t) return ${leafObj}`)
  if (!meta.rose) {
    const nodeObj = `{ ${meta.outputs.map(n => `${propKey(n)}: ${em.emitNum(meta.fold.node[n]!)}`).join(', ')} }`
    goLines.push('    const $l = $go($t.left)', '    const $r = $go($t.right)', `    return ${nodeObj}`)
  } else {
    const accNames = Object.keys(meta.roseStart!)
    for (const a of accNames) goLines.push(`    let ${safeVar('$acc_', a)} = ${pEm.emitNum(meta.roseStart![a]!)}`)
    goLines.push('    for (let $i = $t.children.length - 1; $i >= 0; $i--) {', '      const $kid = $go($t.children[$i]!)')
    for (const a of accNames) goLines.push(`      const ${safeVar('$nacc_', a)} = ${em.emitNum(meta.roseStep![a]!)}`)
    for (const a of accNames) goLines.push(`      ${safeVar('$acc_', a)} = ${safeVar('$nacc_', a)}`)
    goLines.push('    }')
    const nodeObj = `{ ${meta.outputs.map(n => `${propKey(n)}: ${em.emitNum(meta.roseNode![n]!)}`).join(', ')} }`
    goLines.push(`    return ${nodeObj}`)
  }
  goLines.push('  }')

  const fnBody: string[] = []
  if (paramChecks.length) fnBody.push(`  if (${paramChecks.join(' || ')}) throw new RangeError(${JSON.stringify(`${meta.name}: invalid params`)})`)
  fnBody.push(...paramScaleLines)
  if (preExpr !== 'true') fnBody.push(`  if (!(${preExpr})) throw new RangeError(${JSON.stringify(`${meta.name}: params violate precondition`)})`)
  fnBody.push(...goLines, '  return $go(tree)')

  const lines: string[] = [
    ...renderHeader({name: meta.name, kind: 'fold', digest, arithmetic: buildArithDesc(decPlaces, roundedPlaces), laws: reports, ...(opts.provenance ? {provenance: opts.provenance} : {})}),
    '',
    hasParams ? `export type Params = {\n${meta.params.map(([n, , k]) => `  readonly ${propKey(n)}: ${kindTsType(k)}`).join('\n')}\n}` : 'export type Params = Record<string, never>',
    '',
    hasInputs ? `export type Input = {\n${meta.inputs.map(([n, , k]) => `  readonly ${propKey(n)}: ${kindTsType(k)}`).join('\n')}\n}` : 'export type Input = Record<string, never>',
    '',
    `export type Result = {\n${meta.outputs.map(n => `  readonly ${propKey(n)}: number`).join('\n')}\n}`,
    '',
    meta.rose
      ? 'export type Tree = { readonly leaf: Input } | { readonly node: Input; readonly children: readonly Tree[] }'
      : 'export type Tree = { readonly leaf: Input } | { readonly node: Input; readonly left: Tree; readonly right: Tree }',
    '',
  ]
  const helperLines = renderTypedHelpers(helpers)
  if (helperLines.length) lines.push(...helperLines, '')
  const usesP = fnBody.some(l => /\bparams\b/.test(l))
  const sig = hasParams ? `(tree: Tree, ${usesP ? 'params: Params' : '_params: Params'}): Result` : '(tree: Tree, _params: Params = {}): Result'
  lines.push(`export function ${fnName}${sig} {`, ...fnBody, '}', '')

  return {
    source: lines.join('\n'),
    digest,
    version: GDP_WIRED_VERSION,
    name: meta.name,
    kind: 'fold',
    exportName: fnName,
    laws: reports,
    allProven,
  }
}

// --- emitLoop (LoopRule) ---------------------------------------------------------------------------------------------

export function emitLoop(l: AnyLoop, opts: EmitLoopOptions = {}): EmitResult {
  const meta = inspectLoopMeta(l)
  const laws: Law[] = opts.laws !== undefined ? [...opts.laws] : [...meta.ownedLaws]
  const digest = loopDigest(meta.loop)
  const reports: EmitLawReport[] = []
  let allProven = true
  let failedVerdict: Verdict | undefined

  if (!opts.allowUnproven || laws.length > 0 || l.hasRank) {
    const v = proveLoop(l, laws, opts.ms !== undefined ? {ms: opts.ms} : {})
    const ok = v.proven && v.checked
    if (!ok) { allProven = false; failedVerdict = v }
    if (laws.length === 0) {
      reports.push({name: 'halts', kind: 'law', proven: ok, checked: ok && v.checked, ...(!ok && v.goal ? {goal: v.goal} : {}), ...(!ok && v.why ? {why: v.why} : {})})
    } else {
      for (const lw of laws) {
        reports.push({name: lw.name, kind: 'law', proven: ok, checked: ok && v.checked, ...(!ok && v.goal ? {goal: v.goal} : {}), ...(!ok && v.why ? {why: v.why} : {})})
      }
    }
  } else {
    allProven = false
  }
  if (!allProven && !opts.allowUnproven) {
    throw new Unproven(
      `${meta.name}: loop termination/laws not proven`,
      failedVerdict ?? {proven: false, checked: false, why: 'loop not proven'},
    )
  }

  const hasParams = meta.params.length > 0
  const hasInputs = meta.inputs.length > 0
  const decPlaces = new Set<number>()
  const roundedPlaces = new Set<number>()
  for (const [, , k] of [...meta.params, ...meta.inputs]) {
    decimalPlacesIn(k, decPlaces)
    decimalRoundedPlacesIn(k, roundedPlaces)
  }

  const helpers = new Set<EmitHelper>()
  const initScaleLines: string[] = []
  const guardScaleLines: string[] = []
  const bodyScaleLines: string[] = []
  const initReg = makeRegistry()
  const guardReg = makeRegistry()
  const bodyReg = makeRegistry()

  for (const [n, , k] of meta.params) {
    if (k.kind === 'decimal') {
      const local = safeVar('$p_', n)
      const call = k.round === 'half-even'
        ? (helpers.add('decRound'), `$decRound(${propAccess('params', n)}, ${k.places}, ${JSON.stringify(n)})`)
        : (helpers.add('dec'), `$dec(${propAccess('params', n)}, ${k.places}, ${10 ** k.places}, ${JSON.stringify(n)})`)
      initScaleLines.push(`  const ${local} = ${call}`)
      guardScaleLines.push(`  const ${local} = ${call}`)
      bodyScaleLines.push(`  const ${local} = ${call}`)
      registerKind(initReg, n, k, local)
      registerKind(guardReg, n, k, local)
      registerKind(bodyReg, n, k, local)
    } else {
      emitFixedPrep(n, k, propAccess('params', n), helpers, initScaleLines)
      emitFixedPrep(n, k, propAccess('params', n), helpers, guardScaleLines)
      emitFixedPrep(n, k, propAccess('params', n), helpers, bodyScaleLines)
      registerKind(initReg, n, k, propAccess('params', n))
      registerKind(guardReg, n, k, propAccess('params', n))
      registerKind(bodyReg, n, k, propAccess('params', n))
    }
  }
  for (const [n, , k] of meta.inputs) {
    if (k.kind === 'decimal') {
      const local = safeVar('$i_', n)
      const call = k.round === 'half-even'
        ? (helpers.add('decRound'), `$decRound(${propAccess('input', n)}, ${k.places}, ${JSON.stringify(n)})`)
        : (helpers.add('dec'), `$dec(${propAccess('input', n)}, ${k.places}, ${10 ** k.places}, ${JSON.stringify(n)})`)
      bodyScaleLines.push(`  const ${local} = ${call}`)
      registerKind(bodyReg, n, k, local)
    } else {
      emitFixedPrep(n, k, propAccess('input', n), helpers, bodyScaleLines)
      registerKind(bodyReg, n, k, propAccess('input', n))
    }
  }
  for (const sn of meta.state) {
    guardReg.slots.set(sn, {kind: 'nat', ts: propAccess('state', sn)})
    bodyReg.slots.set(sn, {kind: 'nat', ts: propAccess('state', sn)})
  }

  const initEm = emitTsCode({reg: initReg, flags: new Map(), maps: new Map(), fns: {}, helpers, fnNames: new Map(), boundKeys: new Map(), cse: new Map()})
  const guardEm = emitTsCode({reg: guardReg, flags: new Map(), maps: new Map(), fns: {}, helpers, fnNames: new Map(), boundKeys: new Map(), cse: new Map()})
  const bodyEm = emitTsCode({reg: bodyReg, flags: new Map(), maps: new Map(), fns: {}, helpers, fnNames: new Map(), boundKeys: new Map(), cse: new Map()})

  const paramChecks = meta.params.flatMap(([n, , k]) => kindGuardChecks(k, propAccess('params', n)))
  const inputChecks = meta.inputs.flatMap(([n, , k]) => kindGuardChecks(k, propAccess('input', n)))
  const preExpr = meta.loop.pre ? initEm.emitCond(meta.loop.pre) : 'true'
  const whileExpr = guardEm.emitCond(meta.loop.while)
  const assumeExpr = meta.loop.assume ? bodyEm.emitCond(meta.loop.assume) : 'true'

  const initLines: string[] = []
  if (paramChecks.length) initLines.push(`  if (${paramChecks.join(' || ')}) throw new RangeError(${JSON.stringify(`${meta.name}: invalid params`)})`)
  initLines.push(...initScaleLines)
  if (preExpr !== 'true') initLines.push(`  if (!(${preExpr})) throw new RangeError(${JSON.stringify(`${meta.name}: params violate precondition`)})`)
  initLines.push('  return {', ...meta.state.map(sn => `    ${propKey(sn)}: ${initEm.emitNum(meta.loop.state[sn]!)},`), '  }')

  const guardLines: string[] = [...guardScaleLines, `  return ${whileExpr}`]

  const bodyLines: string[] = []
  if (inputChecks.length) bodyLines.push(`  if (${inputChecks.join(' || ')}) throw new RangeError(${JSON.stringify(`${meta.name}: invalid input`)})`)
  bodyLines.push(...bodyScaleLines)
  if (assumeExpr !== 'true') bodyLines.push(`  if (!(${assumeExpr})) throw new RangeError(${JSON.stringify(`${meta.name}: input violates assumption`)})`)
  bodyLines.push('  return {', ...meta.state.map(sn => `    ${propKey(sn)}: ${meta.loop.body[sn] ? bodyEm.emitNum(meta.loop.body[sn]!) : propAccess('state', sn)},`), '  }')

  const lines: string[] = [
    ...renderHeader({name: meta.name, kind: 'loop', digest, arithmetic: buildArithDesc(decPlaces, roundedPlaces), laws: reports, ...(opts.provenance ? {provenance: opts.provenance} : {})}),
    '',
    hasParams ? `export type Params = {\n${meta.params.map(([n, , k]) => `  readonly ${propKey(n)}: ${kindTsType(k)}`).join('\n')}\n}` : 'export type Params = Record<string, never>',
    '',
    hasInputs ? `export type Input = {\n${meta.inputs.map(([n, , k]) => `  readonly ${propKey(n)}: ${kindTsType(k)}`).join('\n')}\n}` : 'export type Input = Record<string, never>',
    '',
    meta.state.length ? `export type State = {\n${meta.state.map(n => `  readonly ${propKey(n)}: number`).join('\n')}\n}` : 'export type State = Record<string, never>',
    '',
  ]
  const helperLines = renderTypedHelpers(helpers)
  if (helperLines.length) lines.push(...helperLines, '')

  const initP = hasParams ? (initLines.some(ln => /\bparams\b/.test(ln)) ? 'params: Params' : '_params: Params') : '_params: Params = {}'
  const guardP = guardLines.some(ln => /\bparams\b/.test(ln)) ? 'params: Params' : '_params: Params'
  const guardS = guardLines.some(ln => /\bstate\b/.test(ln)) ? 'state: State' : '_state: State'
  const bodyP = bodyLines.some(ln => /\bparams\b/.test(ln)) ? 'params: Params' : '_params: Params'
  const bodyS = bodyLines.some(ln => /\bstate\b/.test(ln)) ? 'state: State' : '_state: State'
  const bodyI = bodyLines.some(ln => /\binput\b/.test(ln)) ? 'input: Input' : '_input: Input'

  lines.push(
    `export function init(${initP}): State {`, ...initLines, '}', '',
    `export function guard(${guardP}, ${guardS}): boolean {`, ...guardLines, '}', '',
    `export function body(${bodyP}, ${bodyS}, ${bodyI}): State {`, ...bodyLines, '}', '',
    `export function run(params: Params, inputs: readonly Input[]): State {`,
    '  let st = init(params)',
    '  for (const inp of inputs) {',
    '    if (!guard(params, st)) break',
    '    st = body(params, st, inp)',
    '  }',
    '  return st',
    '}', '',
  )

  return {
    source: lines.join('\n'),
    digest,
    version: GDP_WIRED_VERSION,
    name: meta.name,
    kind: 'loop',
    exportName: 'run',
    laws: reports,
    allProven,
  }
}
