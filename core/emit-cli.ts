// CLI for `gdp-wired emit <module>#<export> [--out <file.ts>] [--check] [--verify] [--laws <export>] [--step-laws <export>] [--from any] [--ms 10000] [--json]`.
// `--verify` runs a differential check of the emitted module against the rule's interpreter (exhaustive on small
// finite domains + randomized & edge runs, including error/refusal parity).
// Exit codes:
//   0: emitted (and matched under --check, and differential --verify passed)
//   1: --check drift detected, or --verify found a differential mismatch
//   2: unproven rule/law, bad arguments, missing export, or load failure
import {
  type Decision,
  type EmitBundle,
  type EmitResult,
  type KindInfo,
  type Raw,
  Fun,
  Rule,
  Chart,
  emitChart,
  emitFun,
  emitRatRule,
  emitRule,
  inspectFunMeta,
  inspectRuleMeta,
} from './dsl.ts'
import {type Rand, evalC, seeded} from './machine.ts'
import {allowed as ruleAllowed} from './watch.ts'
import {type RatLaw, RatRule, inspectRatRule, interpretQ} from './rationals.ts'
import {qparse, qshow} from './q.ts'
import type {Law} from './machine.ts'
import type {StepLaw} from '../kernel/kernel.ts'

type FS = {
  existsSync: (p: string) => boolean
  readFileSync: (p: string, e: string) => string
  mkdirSync: (p: string, o: {recursive: boolean}) => unknown
  writeFileSync: (p: string, s: string) => void
  rmSync: (p: string, o: {force: boolean}) => void
}
type Path = {
  resolve: (...p: string[]) => string
  dirname: (p: string) => string
  join: (...p: string[]) => string
  relative: (a: string, b: string) => string
}
type UrlMod = {pathToFileURL: (p: string) => {href: string}}
type OsMod = {tmpdir: () => string}

const proc = (globalThis as unknown as {
  process: {
    cwd: () => string
    pid: number
    stdout: {write: (s: string) => void}
    stderr?: {write: (s: string) => void}
    getBuiltinModule: (id: string) => unknown
  }
}).process
const fs = proc.getBuiltinModule('node:fs') as FS
const path = proc.getBuiltinModule('node:path') as Path
const urlMod = proc.getBuiltinModule('node:url') as UrlMod
const osMod = proc.getBuiltinModule('node:os') as OsMod

const out = (s = '') => proc.stdout.write(`${s}\n`)
const err = (s: string) => (proc.stderr ?? proc.stdout).write(`${s}\n`)

export type EmitCliOptions = {
  target: string
  out?: string
  check?: boolean
  verify?: boolean
  laws?: string
  stepLaws?: string
  name?: string
  from?: 'any'
  ms?: number
  json?: boolean
}

export const EMIT_USAGE = `gdp-wired emit <module>#<export> [--out <file.ts>] [--check] [--verify] [--laws <export>] [--step-laws <export>] [--name <ident>] [--from any] [--ms 10000] [--json]

Emits standalone, zero-dependency TypeScript source from a proven Rule, Fun, RatRule, Chart, or EmitBundle export.
  --out <file.ts>     Write generated TypeScript to <file.ts> (required for --check)
  --check             Regenerate in memory and exit 1 with a short diff if <file.ts> differs or is missing
  --verify            Differentially check the emitted module against the rule's interpreter (exhaustive small + randomized)
  --laws <export>     Export name in <module> holding the laws array (or function returning it)
  --step-laws <exp>   Export name in <module> holding the step laws array (or function returning it)
  --name <ident>      Override generated function name
  --from any          Prove invariants from every state allowed by the laws
  --ms <ms>           Proof search budget in milliseconds (default 10000)
  --json              Output structured JSON result

Exit codes: 0 ok; 1 --check diff or --verify mismatch; 2 unproven rule/law or error.`

export function parseEmitArgs(argv: string[]): {ok: true, opts: EmitCliOptions} | {ok: false, help?: boolean, error: string} {
  let target = ''
  const opts: EmitCliOptions = {target: ''}
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i]!
    if (a === '--help' || a === '-h' || a === 'help') return {ok: false, help: true, error: EMIT_USAGE}
    else if (a === '--check') opts.check = true
    else if (a === '--verify') opts.verify = true
    else if (a === '--json') opts.json = true
    else if (a.startsWith('--')) {
      const eq = a.indexOf('=')
      const k = eq >= 0 ? a.slice(2, eq) : a.slice(2)
      const v = eq >= 0 ? a.slice(eq + 1) : (argv[++i] ?? '')
      if (!v) return {ok: false, error: `gdp-wired emit: missing value for --${k}`}
      if (k === 'out') opts.out = v
      else if (k === 'laws') opts.laws = v
      else if (k === 'step-laws' || k === 'stepLaws') opts.stepLaws = v
      else if (k === 'name') opts.name = v
      else if (k === 'from') {
        if (v !== 'any') return {ok: false, error: `gdp-wired emit: --from takes 'any', not ${v}`}
        opts.from = 'any'
      } else if (k === 'ms') {
        const n = Number(v)
        if (!Number.isFinite(n) || n <= 0) return {ok: false, error: `gdp-wired emit: invalid --ms ${v}`}
        opts.ms = n
      } else return {ok: false, error: `gdp-wired emit: unknown flag --${k}`}
    } else if (!target) {
      target = a
    } else {
      return {ok: false, error: `gdp-wired emit: unexpected argument ${a}`}
    }
  }
  if (!target) return {ok: false, help: true, error: EMIT_USAGE}
  opts.target = target
  if (opts.check && !opts.out) return {ok: false, error: 'gdp-wired emit: --check requires --out <file.ts>'}
  return {ok: true, opts}
}

export function shortDiff(expected: string, actual: string, maxLines = 40): string {
  const a = expected.split('\n'), b = actual.split('\n')
  const outLines: string[] = []
  let shown = 0
  const max = Math.max(a.length, b.length)
  for (let i = 0; i < max; i++) {
    if (a[i] === b[i]) continue
    if (shown >= maxLines) { outLines.push('  ... (diff truncated)'); break }
    outLines.push(`@@ line ${i + 1} @@`)
    if (i < a.length) { outLines.push(`- ${a[i]!}`); shown++ }
    if (i < b.length) { outLines.push(`+ ${b[i]!}`); shown++ }
  }
  return outLines.join('\n')
}

function resolveLawExport<T>(mod: Record<string, unknown>, exportName: string, target: unknown): T[] {
  if (!(exportName in mod)) throw new Error(`export "${exportName}" not found in module`)
  const raw = mod[exportName]
  const val = typeof raw === 'function' ? (raw as (t: unknown) => unknown)(target) : raw
  if (Array.isArray(val)) return val as T[]
  if (val && typeof val === 'object') return [val as T]
  throw new Error(`export "${exportName}" must be a law, array of laws, or function returning laws`)
}

function isEmitBundle(v: unknown): v is EmitBundle {
  return typeof v === 'object' && v !== null && ('rule' in v || 'fun' in v || 'ratRule' in v || 'chart' in v)
}

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyRule = Rule<any, any, any, any, any, any, any, any>
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyFun = Fun<any, any, any>
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyRatRule = RatRule<any, any, any>
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyChart = Chart<any, any, any>

export type ResolvedTarget =
  | {kind: 'rule', rule: AnyRule}
  | {kind: 'fun', fun: AnyFun, defaultParams?: Readonly<Record<string, Raw>>}
  | {kind: 'ratRule', ratRule: AnyRatRule}
  | {kind: 'chart', chart: AnyChart}

export async function resolveAndEmit(opts: EmitCliOptions): Promise<{resolved: ResolvedTarget, result: EmitResult}> {
  const hash = opts.target.lastIndexOf('#')
  if (hash <= 0 || hash === opts.target.length - 1) throw new Error(`expected <module>#<export>, got "${opts.target}"`)
  const modPath = path.resolve(proc.cwd(), opts.target.slice(0, hash))
  const expName = opts.target.slice(hash + 1)
  if (!fs.existsSync(modPath)) throw new Error(`module not found: ${opts.target.slice(0, hash)}`)

  const mod = await import(urlMod.pathToFileURL(modPath).href) as Record<string, unknown>
  if (!(expName in mod)) {
    throw new Error(`export "${expName}" not found in ${opts.target.slice(0, hash)} (exports: ${Object.keys(mod).join(', ') || 'none'})`)
  }
  const target = mod[expName]

  if (target instanceof Rule) {
    const laws = opts.laws ? resolveLawExport<Law>(mod, opts.laws, target) : undefined
    const stepLaws = opts.stepLaws ? resolveLawExport<StepLaw>(mod, opts.stepLaws, target) : undefined
    return {
      resolved: {kind: 'rule', rule: target as never},
      result: emitRule(target, {...(laws ? {laws} : {}), ...(stepLaws ? {stepLaws} : {}), ...(opts.name ? {name: opts.name} : {}), ...(opts.from ? {from: opts.from} : {}), ...(opts.ms !== undefined ? {ms: opts.ms} : {}), allowUnproven: true}),
    }
  }
  if (target instanceof Fun) {
    const laws = opts.laws ? resolveLawExport<Decision>(mod, opts.laws, target) : undefined
    return {
      resolved: {kind: 'fun', fun: target as never},
      result: emitFun(target, {...(laws ? {laws} : {}), ...(opts.name ? {name: opts.name} : {}), ...(opts.ms !== undefined ? {ms: opts.ms} : {}), allowUnproven: true}),
    }
  }
  if (target instanceof RatRule) {
    const laws = opts.laws ? resolveLawExport<RatLaw<string, string>>(mod, opts.laws, target) : undefined
    return {
      resolved: {kind: 'ratRule', ratRule: target as never},
      result: emitRatRule(target, {...(laws ? {laws} : {}), ...(opts.name ? {name: opts.name} : {}), ...(opts.ms !== undefined ? {ms: opts.ms} : {}), allowUnproven: true}),
    }
  }
  if (target instanceof Chart) {
    const laws = opts.laws ? resolveLawExport<Law>(mod, opts.laws, target) : undefined
    const stepLaws = opts.stepLaws ? resolveLawExport<StepLaw>(mod, opts.stepLaws, target) : undefined
    return {
      resolved: {kind: 'chart', chart: target as never},
      result: emitChart(target, {...(laws ? {laws} : {}), ...(stepLaws ? {stepLaws} : {}), ...(opts.name ? {name: opts.name} : {}), ...(opts.from ? {from: opts.from} : {}), ...(opts.ms !== undefined ? {ms: opts.ms} : {}), allowUnproven: true}),
    }
  }
  if (isEmitBundle(target)) {
    if ('rule' in target) {
      const laws = opts.laws ? resolveLawExport<Law>(mod, opts.laws, target.rule) : target.laws
      const stepLaws = opts.stepLaws ? resolveLawExport<StepLaw>(mod, opts.stepLaws, target.rule) : target.stepLaws
      return {
        resolved: {kind: 'rule', rule: target.rule},
        result: emitRule(target.rule, {...(laws ? {laws} : {}), ...(stepLaws ? {stepLaws} : {}), ...(opts.name ?? target.name ? {name: opts.name ?? target.name} : {}), ...(opts.from ?? target.from ? {from: opts.from ?? target.from} : {}), ...(opts.ms ?? target.ms !== undefined ? {ms: opts.ms ?? target.ms} : {}), allowUnproven: true}),
      }
    }
    if ('fun' in target) {
      const laws = opts.laws ? resolveLawExport<Decision>(mod, opts.laws, target.fun) : target.laws
      return {
        resolved: {kind: 'fun', fun: target.fun, ...(target.defaultParams ? {defaultParams: target.defaultParams} : {})},
        result: emitFun(target.fun, {...(laws ? {laws} : {}), ...(target.defaultParams ? {defaultParams: target.defaultParams} : {}), ...(opts.name ?? target.name ? {name: opts.name ?? target.name} : {}), ...(opts.ms ?? target.ms !== undefined ? {ms: opts.ms ?? target.ms} : {}), allowUnproven: true}),
      }
    }
    if ('ratRule' in target) {
      const laws = opts.laws ? resolveLawExport<RatLaw<string, string>>(mod, opts.laws, target.ratRule) : target.laws
      return {
        resolved: {kind: 'ratRule', ratRule: target.ratRule},
        result: emitRatRule(target.ratRule, {...(laws ? {laws} : {}), ...(opts.name ?? target.name ? {name: opts.name ?? target.name} : {}), ...(opts.ms ?? target.ms !== undefined ? {ms: opts.ms ?? target.ms} : {}), allowUnproven: true}),
      }
    }
    if ('chart' in target) {
      const laws = opts.laws ? resolveLawExport<Law>(mod, opts.laws, target.chart) : target.laws
      const stepLaws = opts.stepLaws ? resolveLawExport<StepLaw>(mod, opts.stepLaws, target.chart) : target.stepLaws
      return {
        resolved: {kind: 'chart', chart: target.chart},
        result: emitChart(target.chart, {...(laws ? {laws} : {}), ...(stepLaws ? {stepLaws} : {}), ...(opts.name ?? target.name ? {name: opts.name ?? target.name} : {}), ...(opts.from ?? target.from ? {from: opts.from ?? target.from} : {}), ...(opts.ms ?? target.ms !== undefined ? {ms: opts.ms ?? target.ms} : {}), allowUnproven: true}),
      }
    }
  }
  throw new Error(`export "${expName}" is not a Rule, Fun, RatRule, Chart, or EmitBundle`)
}

// --- Differential verification against the interpreter ---------------------------------------------------------------

export type VerifyDiffResult = {
  readonly ok: boolean
  readonly exit: 0 | 1 | 2
  readonly checked: number
  readonly exhaustive: boolean
  readonly throwsMatched: number
  readonly mismatch?: string
}

function deepEq(a: unknown, b: unknown): boolean {
  if (Object.is(a, b)) return true
  if (typeof a === 'number' && typeof b === 'number' && a === b) return true
  if (typeof a !== 'object' || typeof b !== 'object' || a === null || b === null) return false
  if (Array.isArray(a) || Array.isArray(b)) {
    return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => deepEq(x, b[i]))
  }
  const ka = Object.keys(a), kb = Object.keys(b)
  return ka.length === kb.length && ka.every(k => Object.hasOwn(b, k) && deepEq((a as Record<string, unknown>)[k], (b as Record<string, unknown>)[k]))
}

function finiteValues(k: KindInfo, cap: number): Raw[] | undefined {
  if (cap < 1) return undefined
  switch (k.kind) {
    case 'bool': return cap >= 2 ? [false, true] : undefined
    case 'oneOf': return k.values.length <= cap ? [...k.values] : undefined
    case 'nat': return k.max !== undefined && k.max + 1 <= cap ? Array.from({length: k.max + 1}, (_, i) => i) : undefined
    case 'maybe': {
      const inner = finiteValues(k.of, cap - 1)
      return inner ? [null, ...inner] : undefined
    }
    case 'record': return finiteRecord(k.fields, cap)
    case 'variant': {
      const out: Raw[] = []
      for (const [c, fs] of k.cases) {
        const sub = finiteRecord(fs, cap - out.length)
        if (!sub) return undefined
        for (const obj of sub) out.push({[k.tagKey]: c, ...(obj as Record<string, Raw>)})
      }
      return out
    }
    default: return undefined
  }
}

function finiteRecord(fields: readonly [string, KindInfo][], cap: number): Record<string, Raw>[] | undefined {
  let acc: Record<string, Raw>[] = [{}]
  for (const [name, k] of fields) {
    const vals = finiteValues(k, Math.floor(cap / acc.length))
    if (!vals) return undefined
    const next: Record<string, Raw>[] = []
    for (const base of acc) for (const v of vals) next.push({...base, [name]: v})
    acc = next
    if (acc.length > cap) return undefined
  }
  return acc
}

function sampleDecimalPool(places: number, hints: readonly number[]): number[] {
  const unit = 1 / 10 ** places
  const base = [0, unit, 0.1, 0.25, 0.5, 0.75, 1 - unit, 1]
  const out = new Set<number>(base)
  for (const h of hints) {
    if (Number.isFinite(h)) {
      const s = Math.round(h * 10 ** places)
      for (const d of [-1, 0, 1]) {
        const v = (s + d) / 10 ** places
        if (v >= 0 && v <= 1) out.add(v)
      }
    }
  }
  return [...out]
}

function sampleKind(k: KindInfo, rand: Rand, bound: number, hints: readonly number[]): Raw {
  switch (k.kind) {
    case 'nat': {
      const top = k.max ?? bound
      if (rand(8) === 0) return 0
      if (rand(8) === 0) return top
      return rand(top + 1)
    }
    case 'int': return rand(2 * bound + 1) - bound
    case 'decimal': {
      const pool = sampleDecimalPool(k.places, hints)
      if (rand(2) === 0) return pool[rand(pool.length)]!
      const scale = 10 ** k.places
      return rand(scale + 1) / scale
    }
    case 'bool': return rand(2) === 1
    case 'oneOf': return k.values[rand(k.values.length)]!
    case 'maybe': return rand(4) === 0 ? null : sampleKind(k.of, rand, bound, hints)
    case 'record': return Object.fromEntries(k.fields.map(([f, fk]) => [f, sampleKind(fk, rand, bound, hints)]))
    case 'variant': {
      const [c, fs] = k.cases[rand(k.cases.length)]!
      return {[k.tagKey]: c, ...Object.fromEntries(fs.map(([f, fk]) => [f, sampleKind(fk, rand, bound, hints)]))}
    }
    case 'str': {
      const pool = ['', ...k.patterns.flatMap(p => [p.replaceAll('*', ''), p.replaceAll('*', 'x')]), 'a', 'ab']
      const s = pool[rand(pool.length)]!
      return k.maxLength !== undefined ? s.slice(0, k.maxLength) : s
    }
    default: return rand(bound + 1)
  }
}

let importBust = 0

export async function verifyEmittedFile(
  filePath: string,
  resolved: ResolvedTarget,
  res: EmitResult,
  opts: {trials?: number, runs?: number, steps?: number} = {},
): Promise<VerifyDiffResult> {
  let mod: Record<string, unknown>
  try {
    const href = `${urlMod.pathToFileURL(path.resolve(filePath)).href}?v=${++importBust}`
    mod = await import(href) as Record<string, unknown>
  } catch (e) {
    return {ok: false, exit: 2, checked: 0, exhaustive: false, throwsMatched: 0, mismatch: `failed to load emitted module: ${e instanceof Error ? e.message : String(e)}`}
  }

  const rand = seeded(42)
  let checked = 0
  let throwsMatched = 0

  if (resolved.kind === 'fun') {
    const fn = mod[res.exportName] as ((a: Record<string, Raw>, p?: Record<string, Raw>) => Record<string, Raw>) | undefined
    if (typeof fn !== 'function') return {ok: false, exit: 2, checked: 0, exhaustive: false, throwsMatched: 0, mismatch: `emitted module missing exported function ${res.exportName}`}
    const meta = inspectFunMeta(resolved.fun)
    const fRule = meta.rule, fMachine = fRule.machine, interp = fRule.interpreter({compileHelpers: true})
    const hasParams = meta.params.length > 0
    const defaultP = resolved.defaultParams ?? (typeof mod.defaultParams === 'function' ? (mod.defaultParams as () => Record<string, Raw>)() : undefined)
    const hints = defaultP ? Object.values(defaultP).filter((v): v is number => typeof v === 'number') : []

    // Build parameter sets to test (defaultParams + randomized valid params)
    const paramSets: Record<string, Raw>[] = []
    if (!hasParams) {
      paramSets.push({})
    } else {
      if (defaultP) paramSets.push({...defaultP})
      for (let i = 0; i < 4; i++) {
        const cand = Object.fromEntries(meta.params.map(([n, , k]) => [n, sampleKind(k, rand, 12, hints)]))
        try {
          const ps = fRule.encodeParams(cand as never)
          if (!fMachine.pre || evalC(fMachine.pre, ps, {scalars: {}, maps: {}}, fMachine)) paramSets.push(cand)
        } catch { /* retry */ }
      }
      if (!paramSets.length) paramSets.push(Object.fromEntries(meta.params.map(([n, k]) => [n, k.empty()])))
    }

    const finInputs = finiteRecord(meta.inputs.map(([n, , k]) => [n, k]), 4096)
    const evalInterp = (args: Record<string, Raw>, params: Record<string, Raw>): {ok: true, val: Record<string, Raw>} | {ok: false, err: string} => {
      try {
        const ps = fRule.encodeParams(params as never)
        if (fMachine.pre && !evalC(fMachine.pre, ps, {scalars: {}, maps: {}}, fMachine)) return {ok: false, err: 'pre'}
        const st0 = interp.init(ps)
        const inp = fRule.encodeInput(args as never, params as never)
        if (!ruleAllowed(fMachine, interp, ps, st0, inp)) return {ok: false, err: 'assume'}
        const st1 = fRule.decode(interp.step(ps, st0, inp))
        return {ok: true, val: Object.fromEntries(meta.outputs.map(([n]) => [n, st1[`out.${n}`]!]))}
      } catch (e) {
        return {ok: false, err: e instanceof Error ? e.message : String(e)}
      }
    }
    const evalEmit = (args: Record<string, Raw>, params: Record<string, Raw>): {ok: true, val: Record<string, Raw>} | {ok: false, err: string} => {
      try {
        return {ok: true, val: hasParams ? fn(args, params) : fn(args)}
      } catch (e) {
        return {ok: false, err: e instanceof Error ? e.message : String(e)}
      }
    }

    const checkOne = (args: Record<string, Raw>, params: Record<string, Raw>): string | undefined => {
      const want = evalInterp(args, params)
      const got = evalEmit(args, params)
      checked++
      if (want.ok !== got.ok) {
        return `at args=${JSON.stringify(args)}, params=${JSON.stringify(params)}: ${want.ok ? `interpreter returned ${JSON.stringify(want.val)}, emitted threw (${(got as {err: string}).err})` : `interpreter refused (${(want as {err: string}).err}), emitted returned ${JSON.stringify((got as {val: unknown}).val)}`}`
      }
      if (!want.ok) { throwsMatched++; return undefined }
      if (!deepEq(got.val, want.val)) {
        return `at args=${JSON.stringify(args)}, params=${JSON.stringify(params)}: emitted ${JSON.stringify(got.val)} !== interpreter ${JSON.stringify(want.val)}`
      }
      return undefined
    }

    // 1. Exhaustive finite inputs or randomized + edge inputs
    const trials = opts.trials ?? 250
    for (const p of paramSets) {
      if (finInputs) {
        for (const args of finInputs) {
          const diff = checkOne(args, p)
          if (diff) return {ok: false, exit: 1, checked, exhaustive: false, throwsMatched, mismatch: diff}
        }
      } else {
        for (let i = 0; i < trials; i++) {
          const args = Object.fromEntries(meta.inputs.map(([n, , k]) => [n, sampleKind(k, rand, 20, hints)]))
          const diff = checkOne(args, p)
          if (diff) return {ok: false, exit: 1, checked, exhaustive: false, throwsMatched, mismatch: diff}
        }
      }
      // 2. Explicit precision/range error parity probes (including >p decimal places like 0.73219!)
      for (const [n, , k] of meta.inputs) {
        const base = Object.fromEntries(meta.inputs.map(([fn0, fk0]) => [fn0, fk0.empty()]))
        const probes: Raw[] = k.kind === 'decimal'
          ? [0.73219, 0.00001, -0.0001, 1.0001, Number.NaN]
          : k.kind === 'nat'
            ? [-1, 1.5, ...(k.max !== undefined ? [k.max + 1] : [])]
            : []
        for (const probe of probes) {
          const diff = checkOne({...base, [n]: probe}, p)
          if (diff) return {ok: false, exit: 1, checked, exhaustive: false, throwsMatched, mismatch: diff}
        }
      }
    }
    return {ok: true, exit: 0, checked, exhaustive: !!finInputs && (!hasParams || !!finiteRecord(meta.params.map(([n, , k]) => [n, k]), 64)), throwsMatched}
  }

  if (resolved.kind === 'rule' || resolved.kind === 'chart') {
    const r = resolved.kind === 'chart' ? resolved.chart.rule : resolved.rule
    const initFn = mod.init as ((p: Record<string, Raw>) => Record<string, unknown>) | undefined
    const stepFn = mod.step as ((p: Record<string, Raw>, s: Record<string, unknown>, i: Record<string, Raw>) => Record<string, unknown>) | undefined
    if (typeof initFn !== 'function' || typeof stepFn !== 'function') {
      return {ok: false, exit: 2, checked: 0, exhaustive: false, throwsMatched: 0, mismatch: 'emitted module missing exported init/step functions'}
    }
    const meta = inspectRuleMeta(r)
    const m = r.machine
    const interp = r.interpreter({compileHelpers: true})
    const runs = opts.runs ?? 25
    const stepsPerRun = opts.steps ?? 20

    const compareState = (stE: Record<string, unknown>, stI: ReturnType<typeof interp.init>, keysTouched: Set<number>): string | undefined => {
      const dec = r.decode(stI)
      for (const [n] of meta.state) {
        if (!deepEq(stE[n], dec[n])) return `state.${n}: emitted ${JSON.stringify(stE[n])} !== interpreter ${JSON.stringify(dec[n])}`
      }
      for (const [mapName, dflt, cellKind] of meta.maps) {
        const emMap = stE[mapName] as Map<number, unknown>
        const emDef = !cellKind && Object.hasOwn(stE, `${mapName}_default`) ? (stE[`${mapName}_default`] as number) : dflt
        const decMap = (cellKind ? dec[mapName] : undefined) as Record<string, unknown> | undefined
        const allKeys = new Set<number>([...keysTouched, ...emMap.keys(), ...(stI.maps[mapName]?.keys() ?? []), 0, 1])
        if (decMap) for (const k of Object.keys(decMap)) allKeys.add(Number(k))
        for (const k of allKeys) {
          const got = emMap.get(k) ?? (cellKind ? emptyVal(cellKind) : emDef)
          const want = cellKind
            ? (decMap?.[String(k)] ?? emptyVal(cellKind))
            : (stI.maps[mapName]?.get(k) ?? stI.defaults?.[mapName] ?? dflt)
          if (!deepEq(got, want)) return `state.${mapName}[${k}]: emitted ${JSON.stringify(got)} !== interpreter ${JSON.stringify(want)}`
        }
      }
      for (const [itemName] of meta.items) {
        if (!deepEq(stE[itemName], dec[itemName])) return `state.${itemName}: emitted ${JSON.stringify(stE[itemName])} !== interpreter ${JSON.stringify(dec[itemName])}`
      }
      return undefined
    }

    let exhaustive = false
    for (let runIdx = 0; runIdx < runs; runIdx++) {
      // Sample valid params
      let pRaw: Record<string, Raw> = {}, ps: Record<string, number> = {}
      let validP = false
      for (let attempt = 0; attempt < 30; attempt++) {
        pRaw = Object.fromEntries(meta.params.map(([n, , k]) => [n, sampleKind(k, rand, 12, [])]))
        try {
          ps = r.encodeParams(pRaw as never)
          if (!m.pre || evalC(m.pre, ps, {scalars: {}, maps: {}}, m)) { validP = true; break }
        } catch { /* retry */ }
      }
      if (!validP) continue

      let stI = interp.init(ps)
      let stE: Record<string, unknown>
      try { stE = initFn(pRaw) } catch (e) {
        return {ok: false, exit: 1, checked, exhaustive, throwsMatched, mismatch: `init(${JSON.stringify(pRaw)}) threw: ${e instanceof Error ? e.message : String(e)}`}
      }
      const keysTouched = new Set<number>([0, 1, 2])
      const initDiff = compareState(stE, stI, keysTouched)
      checked++
      if (initDiff) return {ok: false, exit: 1, checked, exhaustive, throwsMatched, mismatch: `init(${JSON.stringify(pRaw)}): ${initDiff}`}

      const trace: Record<string, Raw>[] = []
      let monoClock = 0
      for (let s = 0; s < stepsPerRun; s++) {
        const iRaw = Object.fromEntries(meta.inputs.map(([n, , k]) => {
          if (k.kind === 'nat' && (n === 't' || n === 'now' || n === r.orderedBy)) { monoClock += rand(8); return [n, monoClock] }
          return [n, sampleKind(k, rand, 15, [])]
        }))
        for (const v of Object.values(iRaw)) if (typeof v === 'number' && Number.isInteger(v) && v >= 0 && v < 1000) keysTouched.add(v)
        let enc: ReturnType<typeof r.encodeInput>
        let interpAllowed = false
        try {
          enc = r.encodeInput(iRaw as never, pRaw as never)
          interpAllowed = ruleAllowed(m, interp, ps, stI, enc)
        } catch {
          interpAllowed = false
          enc = {}
        }
        let nextI: {ok: true, st: typeof stI} | {ok: false, err: string}
        if (!interpAllowed) {
          nextI = {ok: false, err: 'not allowed'}
        } else {
          try { nextI = {ok: true, st: interp.step(ps, stI, enc)} } catch (e) { nextI = {ok: false, err: e instanceof Error ? e.message : String(e)} }
        }
        let nextE: {ok: true, st: Record<string, unknown>} | {ok: false, err: string}
        try { nextE = {ok: true, st: stepFn(pRaw, stE, iRaw)} } catch (e) { nextE = {ok: false, err: e instanceof Error ? e.message : String(e)} }
        checked++
        if (nextI.ok !== nextE.ok) {
          return {ok: false, exit: 1, checked, exhaustive, throwsMatched, mismatch: `params=${JSON.stringify(pRaw)}, step ${s}, input=${JSON.stringify(iRaw)}: ${nextI.ok ? `interpreter succeeded, emitted threw (${(nextE as {err: string}).err})` : `interpreter refused (${(nextI as {err: string}).err}), emitted succeeded`}`}
        }
        if (!nextI.ok) { throwsMatched++; continue }
        stI = nextI.st
        stE = (nextE as {ok: true, st: Record<string, unknown>}).st
        trace.push(iRaw)
        const diff = compareState(stE, stI, keysTouched)
        if (diff) {
          return {ok: false, exit: 1, checked, exhaustive, throwsMatched, mismatch: `params=${JSON.stringify(pRaw)}, step ${s}, trace=${JSON.stringify(trace)}: ${diff}`}
        }
      }
    }
    return {ok: true, exit: 0, checked, exhaustive, throwsMatched}
  }

  // RatRule differential verification against interpretQ
  const meta = inspectRatRule(resolved.ratRule)
  const qInterp = interpretQ(meta.machine)
  const toRat = mod.toRat as ((x: unknown) => readonly [bigint, bigint]) | undefined
  const formatRat = mod.formatRat as ((r: readonly [bigint, bigint]) => string) | undefined
  const initFn = mod.init as ((p: Record<string, readonly [bigint, bigint]>) => Record<string, readonly [bigint, bigint]>) | undefined
  const allowedFn = mod.allowed as ((p: Record<string, readonly [bigint, bigint]>, s: Record<string, readonly [bigint, bigint]>, i: Record<string, readonly [bigint, bigint]>) => boolean) | undefined
  const stepFn = mod.step as ((p: Record<string, readonly [bigint, bigint]>, s: Record<string, readonly [bigint, bigint]>, i: Record<string, readonly [bigint, bigint]>) => Record<string, readonly [bigint, bigint]>) | undefined
  if (!toRat || !formatRat || !initFn || !allowedFn || !stepFn) {
    return {ok: false, exit: 2, checked: 0, exhaustive: false, throwsMatched: 0, mismatch: 'emitted RatRule module missing required exports'}
  }
  const ratPoolNonneg = ['0', '0.1', '1/3', '0.25', '0.4', '0.5', '2/3', '1', '2', '12.50', '999999.99']
  const ratPoolAny = ['-2', '-1/3', '0', '0.1', '1/3', '0.5', '1', '2', '3']
  for (let runIdx = 0; runIdx < (opts.runs ?? 25); runIdx++) {
    const pRaw = Object.fromEntries(meta.params.map(([n, k]) => [n, (k.nonneg ? ratPoolNonneg : ratPoolAny)[rand((k.nonneg ? ratPoolNonneg : ratPoolAny).length)]!]))
    const pQ = Object.fromEntries(Object.entries(pRaw).map(([n, v]) => [n, qparse(v)]))
    const pE = Object.fromEntries(Object.entries(pRaw).map(([n, v]) => [n, toRat(v)]))
    let stQ = qInterp.init(pQ), stE = initFn(pE)
    checked++
    for (const s of meta.state) {
      if (formatRat(stE[s]!) !== qshow(stQ[s]!)) {
        return {ok: false, exit: 1, checked, exhaustive: false, throwsMatched, mismatch: `RatRule init(${JSON.stringify(pRaw)}).${s}: emitted ${formatRat(stE[s]!)} !== interpreter ${qshow(stQ[s]!)}`}
      }
    }
    for (let stepIdx = 0; stepIdx < (opts.steps ?? 15); stepIdx++) {
      const iRaw = Object.fromEntries(meta.inputs.map(([n, k]) => [n, (k.nonneg ? ratPoolNonneg : ratPoolAny)[rand((k.nonneg ? ratPoolNonneg : ratPoolAny).length)]!]))
      const iQ = Object.fromEntries(Object.entries(iRaw).map(([n, v]) => [n, qparse(v)]))
      const iE = Object.fromEntries(Object.entries(iRaw).map(([n, v]) => [n, toRat(v)]))
      const okQ = qInterp.allowed(pQ, stQ, iQ), okE = allowedFn(pE, stE, iE)
      checked++
      if (okQ !== okE) {
        return {ok: false, exit: 1, checked, exhaustive: false, throwsMatched, mismatch: `RatRule allowed mismatch at ${JSON.stringify(iRaw)}: emitted ${okE} !== interpreter ${okQ}`}
      }
      if (!okQ) {
        let threw = false
        try { stepFn(pE, stE, iE) } catch { threw = true }
        if (!threw) return {ok: false, exit: 1, checked, exhaustive: false, throwsMatched, mismatch: `RatRule step did not refuse disallowed input ${JSON.stringify(iRaw)}`}
        throwsMatched++
        continue
      }
      stQ = qInterp.step(pQ, stQ, iQ)
      stE = stepFn(pE, stE, iE)
      for (const s of meta.state) {
        if (formatRat(stE[s]!) !== qshow(stQ[s]!)) {
          return {ok: false, exit: 1, checked, exhaustive: false, throwsMatched, mismatch: `RatRule step ${stepIdx} (${JSON.stringify(iRaw)}).${s}: emitted ${formatRat(stE[s]!)} !== interpreter ${qshow(stQ[s]!)}`}
        }
      }
    }
  }
  return {ok: true, exit: 0, checked, exhaustive: false, throwsMatched}
}

function emptyVal(k: KindInfo): Raw {
  switch (k.kind) {
    case 'nat': case 'int': case 'decimal': case 'unknown': return 0
    case 'bool': return false
    case 'oneOf': return k.values[0]!
    case 'maybe': return null
    case 'record': return Object.fromEntries(k.fields.map(([f, fk]) => [f, emptyVal(fk)]))
    case 'variant': {
      const [c, fs] = k.cases[0]!
      return {[k.tagKey]: c, ...Object.fromEntries(fs.map(([f, fk]) => [f, emptyVal(fk)]))}
    }
    case 'str': return ''
    case 'fixed': return k.width === 64 ? '0' : 0
  }
}

export async function emitMain(argv: string[]): Promise<number> {
  const parsed = parseEmitArgs(argv)
  if (!parsed.ok) {
    if (parsed.help) { out(parsed.error); return 0 }
    err(parsed.error)
    return 2
  }
  const opts = parsed.opts
  let resolved: ResolvedTarget, res: EmitResult
  try {
    const got = await resolveAndEmit(opts)
    resolved = got.resolved
    res = got.result
  } catch (e) {
    err(`gdp-wired emit: ${e instanceof Error ? e.message : String(e)}`)
    return 2
  }

  if (!res.allProven) {
    const failed = res.laws.filter(l => !(l.proven && l.checked))
    if (opts.json) {
      out(JSON.stringify({ok: false, exit: 2, name: res.name, digest: res.digest, allProven: false, laws: res.laws}, null, 1))
    } else {
      err(`gdp-wired emit: refused "${res.name}" — not all laws are proven`)
      if (res.laws.length === 0) err('  no laws were provided or registered on this target (pass --laws <export>)')
      for (const l of failed) err(`  - [${l.kind}] ${l.name}: ${l.why ?? l.goal ?? 'unproven'}`)
    }
    return 2
  }

  const outPath = opts.out ? path.resolve(proc.cwd(), opts.out) : undefined

  if (opts.check) {
    if (!outPath || !fs.existsSync(outPath)) {
      const msg = `file missing: ${opts.out ?? ''}`
      if (opts.json) out(JSON.stringify({ok: false, exit: 1, check: 'missing', out: opts.out, digest: res.digest}, null, 1))
      else err(`gdp-wired emit --check: ${msg}`)
      return 1
    }
    const existing = fs.readFileSync(outPath, 'utf8')
    if (existing !== res.source) {
      const diffText = shortDiff(existing, res.source)
      if (opts.json) out(JSON.stringify({ok: false, exit: 1, check: 'diff', out: opts.out, digest: res.digest, diff: diffText}, null, 1))
      else {
        err(`gdp-wired emit --check: ${opts.out} is out of date`)
        err(diffText)
      }
      return 1
    }
  } else if (outPath) {
    fs.mkdirSync(path.dirname(outPath), {recursive: true})
    fs.writeFileSync(outPath, res.source)
  }

  let verifyResult: VerifyDiffResult | undefined
  if (opts.verify) {
    let verifyPath = outPath
    let tmpFile: string | undefined
    if (!verifyPath) {
      tmpFile = path.join(osMod.tmpdir(), `gdp-wired-emit-${proc.pid}-${res.digest.slice(7, 19)}.ts`)
      fs.writeFileSync(tmpFile, res.source)
      verifyPath = tmpFile
    }
    try {
      verifyResult = await verifyEmittedFile(verifyPath, resolved, res)
    } finally {
      if (tmpFile) fs.rmSync(tmpFile, {force: true})
    }
    if (!verifyResult.ok) {
      if (opts.json) out(JSON.stringify({ok: false, exit: verifyResult.exit, name: res.name, digest: res.digest, verify: verifyResult}, null, 1))
      else err(`gdp-wired emit --verify: MISMATCH (${verifyResult.checked} checked): ${verifyResult.mismatch ?? 'failed'}`)
      return verifyResult.exit
    }
  }

  if (opts.json) {
    out(JSON.stringify({
      ok: true,
      exit: 0,
      name: res.name,
      kind: res.kind,
      version: res.version,
      digest: res.digest,
      ...(opts.out ? {out: opts.out} : {}),
      laws: res.laws,
      ...(verifyResult ? {verify: verifyResult} : {}),
    }, null, 1))
  } else if (!outPath && !opts.check) {
    proc.stdout.write(res.source)
  } else {
    const rel = outPath ? (path.relative(proc.cwd(), outPath) || outPath) : res.name
    const action = opts.check ? 'up to date' : 'wrote'
    const vText = verifyResult ? `; verified ${verifyResult.checked} differential trials${verifyResult.exhaustive ? ' (exhaustive)' : ''} (${verifyResult.throwsMatched} error checks matched)` : ''
    out(`gdp-wired emit: ${action} ${rel} (${res.laws.length} proven laws, ${res.digest.slice(0, 19)}...${vText})`)
  }
  return 0
}
