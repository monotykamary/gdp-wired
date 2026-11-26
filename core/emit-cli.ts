// CLI for `gdp-wired emit <module>#<export> [--out <file.ts>] [--check] [--verify] [--laws <export>] [--step-laws <export>] [--from any] [--ms 10000] [--json]`.
// Reuses shared CLI primitives (`up`, `parseCliFlags`, `loadFileModule`, `cliFs`/`cliPath`/`cliOut`/`cliErr`) from
// `core/cli-io.ts` (shared with `core/cli.ts`). `--verify` differentially checks the emitted module against the
// proven rule's interpreter (exhaustive small domains + randomized/edge/rounding/error parity).
// Exit codes: 0 ok; 1 --check diff or --verify mismatch; 2 unproven rule/law or error.
import {
  type Decision,
  type EmitBundle,
  type EmitResult,
  type KindInfo,
  type Raw,
  Chart,
  FoldRule,
  Fun,
  LoopRule,
  RoseFold,
  Rule,
  emitChart,
  emitFold,
  emitFun,
  emitLoop,
  emitRatRule,
  emitRule,
  inspectFoldMeta,
  inspectFunMeta,
  inspectLoopMeta,
  inspectRuleMeta,
} from './dsl.ts'
import {type Rand, evalC, evalE, seeded, unreachable} from './machine.ts'
import {allowed as ruleAllowed} from './watch.ts'
import {type RatLaw, RatRule, inspectRatRule, interpretQ} from './rationals.ts'
import {qparse, qshow} from './q.ts'
import type {Law} from './machine.ts'
import type {StepLaw} from '../kernel/kernel.ts'
import {cliErr as err, cliFs as fs, cliOs as osMod, cliOut as out, cliPath as path, cliProc as proc, loadFileModule, parseCliFlags, up} from './cli-io.ts'

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

const BOOL_FLAGS = new Set(['--check', '--verify', '--json', '--help', '-h'])
const KNOWN_FLAGS = new Set(['check', 'verify', 'json', 'out', 'laws', 'stepLaws', 'name', 'from', 'ms'])

export function parseEmitArgs(argv: string[]): {ok: true, opts: EmitCliOptions} | {ok: false, help?: boolean, error: string} {
  if (argv.some(a => a === '--help' || a === '-h' || a === 'help')) return {ok: false, help: true, error: EMIT_USAGE}
  const parsed = parseCliFlags(argv, BOOL_FLAGS)
  if (parsed.missingValue) return {ok: false, error: `gdp-wired emit: missing value for --${parsed.missingValue}`}
  for (const k of Object.keys(parsed.flags)) {
    if (!KNOWN_FLAGS.has(k)) return {ok: false, error: `gdp-wired emit: unknown flag --${k}`}
  }
  if (parsed.positionals.length === 0) return {ok: false, help: true, error: EMIT_USAGE}
  if (parsed.positionals.length > 1) return {ok: false, error: `gdp-wired emit: unexpected argument ${parsed.positionals[1]!}`}
  const f = parsed.flags
  const opts: EmitCliOptions = {
    target: parsed.positionals[0]!,
    ...(f.out ? {out: String(f.out)} : {}),
    ...(f.check ? {check: true} : {}),
    ...(f.verify ? {verify: true} : {}),
    ...(f.json ? {json: true} : {}),
    ...(f.laws ? {laws: String(f.laws)} : {}),
    ...(f.stepLaws ? {stepLaws: String(f.stepLaws)} : {}),
    ...(f.name ? {name: String(f.name)} : {}),
  }
  if (f.from !== undefined) {
    if (f.from !== 'any') return {ok: false, error: `gdp-wired emit: --from takes 'any', not ${String(f.from)}`}
    opts.from = 'any'
  }
  if (f.ms !== undefined) {
    const n = Number(f.ms)
    if (!Number.isFinite(n) || n <= 0) return {ok: false, error: `gdp-wired emit: invalid --ms ${String(f.ms)}`}
    opts.ms = n
  }
  if (opts.check && !opts.out) return {ok: false, error: 'gdp-wired emit: --check requires --out <file.ts>'}
  return {ok: true, opts}
}

export function shortDiff(expected: string, actual: string, maxLines = 40): string {
  const a = expected.split('\n'), b = actual.split('\n'), outLines: string[] = []
  let shown = 0
  for (let i = 0; i < Math.max(a.length, b.length); i++) {
    if (a[i] === b[i]) continue
    if (shown >= maxLines) { outLines.push('  ... (diff truncated)'); break }
    outLines.push(`@@ line ${i + 1} @@`)
    if (i < a.length) { outLines.push(`- ${a[i]!}`); shown++ }
    if (i < b.length) { outLines.push(`+ ${b[i]!}`); shown++ }
  }
  return outLines.join('\n')
}

export function findRepoRoot(startDir: string): string {
  return up(path.resolve(startDir), d => fs.existsSync(path.join(d, '.git'))) ?? path.resolve(proc.cwd())
}

const toRepoRel = (baseDir: string, absPath: string): string => path.relative(baseDir, absPath).split('\\').join('/') || '.'

function resolveLawExport<T>(mod: Record<string, unknown>, exportName: string, target: unknown): T[] {
  if (!(exportName in mod)) throw new Error(`export "${exportName}" not found in module`)
  const raw = mod[exportName]
  const val = typeof raw === 'function' ? (raw as (t: unknown) => unknown)(target) : raw
  if (Array.isArray(val)) return val as T[]
  if (val && typeof val === 'object') return [val as T]
  throw new Error(`export "${exportName}" must be a law, array of laws, or function returning laws`)
}

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

export type ResolvedTarget =
  | {kind: 'rule', rule: AnyRule}
  | {kind: 'fun', fun: AnyFun, defaultParams?: Readonly<Record<string, Raw>>}
  | {kind: 'ratRule', ratRule: AnyRatRule}
  | {kind: 'chart', chart: AnyChart}
  | {kind: 'fold', fold: AnyFold}
  | {kind: 'loop', loop: AnyLoop}

const isEmitBundle = (v: unknown): v is EmitBundle => typeof v === 'object' && v !== null && ('rule' in v || 'fun' in v || 'ratRule' in v || 'chart' in v || 'fold' in v || 'loop' in v)

export async function resolveAndEmit(opts: EmitCliOptions): Promise<{resolved: ResolvedTarget, result: EmitResult}> {
  const hash = opts.target.lastIndexOf('#')
  if (hash <= 0 || hash === opts.target.length - 1) throw new Error(`expected <module>#<export>, got "${opts.target}"`)
  const modPath = path.resolve(proc.cwd(), opts.target.slice(0, hash)), expName = opts.target.slice(hash + 1)
  if (!fs.existsSync(modPath)) throw new Error(`module not found: ${opts.target.slice(0, hash)}`)

  const repoRoot = findRepoRoot(path.dirname(modPath))
  const outAbs = opts.out ? path.resolve(proc.cwd(), opts.out) : undefined
  const provenance = {model: `${toRepoRel(repoRoot, modPath)}#${expName}`, ...(outAbs ? {out: toRepoRel(repoRoot, outAbs)} : {})}

  const mod = await loadFileModule(modPath)
  if (!(expName in mod)) throw new Error(`export "${expName}" not found in ${opts.target.slice(0, hash)} (exports: ${Object.keys(mod).join(', ') || 'none'})`)
  const rawTarget = mod[expName]
  const bundle: EmitBundle | undefined =
    rawTarget instanceof Rule ? {rule: rawTarget}
    : rawTarget instanceof Fun ? {fun: rawTarget}
    : rawTarget instanceof RatRule ? {ratRule: rawTarget}
    : rawTarget instanceof Chart ? {chart: rawTarget}
    : rawTarget instanceof FoldRule || rawTarget instanceof RoseFold ? {fold: rawTarget}
    : rawTarget instanceof LoopRule ? {loop: rawTarget}
    : isEmitBundle(rawTarget) ? rawTarget : undefined
  if (!bundle) throw new Error(`export "${expName}" is not a Rule, Fun, RatRule, Chart, FoldRule, RoseFold, LoopRule, or EmitBundle`)

  const name = opts.name ?? bundle.name
  const ms = opts.ms ?? bundle.ms
  const common = {...(name ? {name} : {}), ...(ms !== undefined ? {ms} : {}), provenance, allowUnproven: true}

  if ('rule' in bundle) {
    const laws = opts.laws ? resolveLawExport<Law>(mod, opts.laws, bundle.rule) : bundle.laws
    const stepLaws = opts.stepLaws ? resolveLawExport<StepLaw>(mod, opts.stepLaws, bundle.rule) : bundle.stepLaws
    const from = opts.from ?? bundle.from
    return {
      resolved: {kind: 'rule', rule: bundle.rule},
      result: emitRule(bundle.rule, {...(laws ? {laws} : {}), ...(stepLaws ? {stepLaws} : {}), ...(from ? {from} : {}), ...common}),
    }
  }
  if ('fun' in bundle) {
    const laws = opts.laws ? resolveLawExport<Decision>(mod, opts.laws, bundle.fun) : bundle.laws
    return {
      resolved: {kind: 'fun', fun: bundle.fun, ...(bundle.defaultParams ? {defaultParams: bundle.defaultParams} : {})},
      result: emitFun(bundle.fun, {...(laws ? {laws} : {}), ...(bundle.defaultParams ? {defaultParams: bundle.defaultParams} : {}), ...common}),
    }
  }
  if ('ratRule' in bundle) {
    const laws = opts.laws ? resolveLawExport<RatLaw<string, string>>(mod, opts.laws, bundle.ratRule) : bundle.laws
    return {
      resolved: {kind: 'ratRule', ratRule: bundle.ratRule},
      result: emitRatRule(bundle.ratRule, {...(laws ? {laws} : {}), ...common}),
    }
  }
  if ('fold' in bundle) {
    const laws = opts.laws ? resolveLawExport<Law>(mod, opts.laws, bundle.fold) : bundle.laws
    return {
      resolved: {kind: 'fold', fold: bundle.fold},
      result: emitFold(bundle.fold, {...(laws ? {laws} : {}), ...common}),
    }
  }
  if ('loop' in bundle) {
    const laws = opts.laws ? resolveLawExport<Law>(mod, opts.laws, bundle.loop) : bundle.laws
    return {
      resolved: {kind: 'loop', loop: bundle.loop},
      result: emitLoop(bundle.loop, {...(laws ? {laws} : {}), ...common}),
    }
  }
  const laws = opts.laws ? resolveLawExport<Law>(mod, opts.laws, bundle.chart) : bundle.laws
  const stepLaws = opts.stepLaws ? resolveLawExport<StepLaw>(mod, opts.stepLaws, bundle.chart) : bundle.stepLaws
  const from = opts.from ?? bundle.from
  return {
    resolved: {kind: 'chart', chart: bundle.chart},
    result: emitChart(bundle.chart, {...(laws ? {laws} : {}), ...(stepLaws ? {stepLaws} : {}), ...(from ? {from} : {}), ...common}),
  }
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
  if (Object.is(a, b) || (typeof a === 'number' && typeof b === 'number' && a === b)) return true
  if (typeof a !== 'object' || typeof b !== 'object' || a === null || b === null) return false
  if (Array.isArray(a) || Array.isArray(b)) return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => deepEq(x, b[i]))
  const ka = Object.keys(a), kb = Object.keys(b)
  return ka.length === kb.length && ka.every(k => Object.hasOwn(b, k) && deepEq((a as Record<string, unknown>)[k], (b as Record<string, unknown>)[k]))
}

function finiteValues(k: KindInfo, cap: number): Raw[] | undefined {
  if (cap < 1) return undefined
  switch (k.kind) {
    case 'bool': return cap >= 2 ? [false, true] : undefined
    case 'oneOf': return k.values.length <= cap ? [...k.values] : undefined
    case 'nat': return k.max !== undefined && k.max + 1 <= cap ? Array.from({length: k.max + 1}, (_, i) => i) : undefined
    case 'maybe': { const inner = finiteValues(k.of, cap - 1); return inner ? [null, ...inner] : undefined }
    case 'record': return finiteRecord(k.fields, cap)
    case 'variant': {
      const acc: Raw[] = []
      for (const [c, fs] of k.cases) {
        const sub = finiteRecord(fs, cap - acc.length)
        if (!sub) return undefined
        for (const obj of sub) acc.push({[k.tagKey]: c, ...(obj as Record<string, Raw>)})
      }
      return acc
    }
    case 'int': case 'decimal': case 'str': case 'fixed': case 'unknown': return undefined
    default: return unreachable(k)
  }
}

function finiteRecord(fields: readonly [string, KindInfo][], cap: number): Record<string, Raw>[] | undefined {
  let acc: Record<string, Raw>[] = [{}]
  for (const [name, k] of fields) {
    const vals = finiteValues(k, Math.floor(cap / acc.length))
    if (!vals) return undefined
    acc = acc.flatMap(base => vals.map(v => ({...base, [name]: v})))
    if (acc.length > cap) return undefined
  }
  return acc
}

const DEC_PROBES: readonly number[] = [0.73219, 0.00001, 0.00005, 0.00015, 0.00025, -0.00005, -0.00015, -0.00025, 1e-7, 5e-7, 5e-5, 1.5e-4, 2.5e-4, 0.99995, 0.99996, -0.0001, 1.0001, Number.NaN]
const DEC_HALF_EVEN_POOL: readonly number[] = [0.00005, 0.00015, 0.00025, 0.73219, 1e-7, 5e-7, 5e-5, 1.5e-4, 2.5e-4, 0.99995, 0.99996]

function sampleDecimalPool(places: number, hints: readonly number[]): number[] {
  const scale = 10 ** places, unit = 1 / scale
  const pool = new Set<number>([0, unit, 0.1, 0.25, 0.5, 0.75, 1 - unit, 1])
  for (const h of hints) if (Number.isFinite(h)) {
    const s = Math.round(h * scale)
    for (const d of [-1, 0, 1]) { const v = (s + d) / scale; if (v >= 0 && v <= 1) pool.add(v) }
  }
  return [...pool]
}

function sampleKind(k: KindInfo, rand: Rand, bound: number, hints: readonly number[]): Raw {
  switch (k.kind) {
    case 'nat': { const top = k.max ?? bound; return rand(8) === 0 ? 0 : rand(8) === 0 ? top : rand(top + 1) }
    case 'int': return rand(2 * bound + 1) - bound
    case 'decimal': {
      if (k.round === 'half-even' && rand(3) === 0) return rand(2) === 0 ? DEC_HALF_EVEN_POOL[rand(DEC_HALF_EVEN_POOL.length)]! : rand(1_000_001) / 1_000_000
      const pool = sampleDecimalPool(k.places, hints), scale = 10 ** k.places
      return rand(2) === 0 ? pool[rand(pool.length)]! : rand(scale + 1) / scale
    }
    case 'bool': return rand(2) === 1
    case 'oneOf': return k.values[rand(k.values.length)]!
    case 'maybe': return rand(4) === 0 ? null : sampleKind(k.of, rand, bound, hints)
    case 'record': return Object.fromEntries(k.fields.map(([f, fk]) => [f, sampleKind(fk, rand, bound, hints)]))
    case 'variant': { const [c, fs] = k.cases[rand(k.cases.length)]!; return {[k.tagKey]: c, ...Object.fromEntries(fs.map(([f, fk]) => [f, sampleKind(fk, rand, bound, hints)]))} }
    case 'str': {
      const pool = ['', ...k.patterns.flatMap(p => [p.replaceAll('*', ''), p.replaceAll('*', 'x')]), 'a', 'ab']
      const s = pool[rand(pool.length)]!
      return k.maxLength !== undefined ? s.slice(0, k.maxLength) : s
    }
    case 'fixed': {
      const cap = k.width === 8 ? (k.signed ? 127 : 255) : Math.min(bound, 50)
      const val = k.signed ? rand(2 * Math.min(bound, cap) + 1) - Math.min(bound, cap) : rand(Math.min(bound, cap) + 1)
      return k.width === 64 ? String(val) : val
    }
    case 'unknown': return rand(bound + 1)
    default: return unreachable(k)
  }
}

function emptyVal(k: KindInfo): Raw {
  switch (k.kind) {
    case 'nat': case 'int': case 'decimal': case 'unknown': return 0
    case 'bool': return false
    case 'oneOf': return k.values[0]!
    case 'maybe': return null
    case 'record': return Object.fromEntries(k.fields.map(([f, fk]) => [f, emptyVal(fk)]))
    case 'variant': { const [c, fs] = k.cases[0]!; return {[k.tagKey]: c, ...Object.fromEntries(fs.map(([f, fk]) => [f, emptyVal(fk)]))} }
    case 'str': return ''
    case 'fixed': return k.width === 64 ? '0' : 0
    default: return unreachable(k)
  }
}

type TryRes<T> = {ok: true, val: T} | {ok: false, err: string}
function tryCall<T>(f: () => T): TryRes<T> {
  try { return {ok: true, val: f()} } catch (e) { return {ok: false, err: e instanceof Error ? e.message : String(e)} }
}

let importBust = 0

export async function verifyEmittedFile(
  filePath: string,
  resolved: ResolvedTarget,
  res: EmitResult,
  opts: {trials?: number, runs?: number, steps?: number} = {},
): Promise<VerifyDiffResult> {
  let mod: Record<string, unknown>
  try { mod = await loadFileModule(filePath, `v=${++importBust}`) } catch (e) {
    return {ok: false, exit: 2, checked: 0, exhaustive: false, throwsMatched: 0, mismatch: `failed to load emitted module: ${e instanceof Error ? e.message : String(e)}`}
  }
  const rand = seeded(42)
  let checked = 0, throwsMatched = 0
  const fail1 = (mismatch: string, exhaustive = false): VerifyDiffResult => ({ok: false, exit: 1, checked, exhaustive, throwsMatched, mismatch})

  if (resolved.kind === 'fun') {
    const fn = mod[res.exportName] as ((a: Record<string, Raw>, p?: Record<string, Raw>) => Record<string, Raw>) | undefined
    if (typeof fn !== 'function') return {ok: false, exit: 2, checked: 0, exhaustive: false, throwsMatched: 0, mismatch: `emitted module missing exported function ${res.exportName}`}
    const meta = inspectFunMeta(resolved.fun), fRule = meta.rule, fMachine = fRule.machine, interp = fRule.interpreter({compileHelpers: true})
    const hasParams = meta.params.length > 0
    const defaultP = resolved.defaultParams ?? (typeof mod.defaultParams === 'function' ? (mod.defaultParams as () => Record<string, Raw>)() : undefined)
    const hints = defaultP ? Object.values(defaultP).filter((v): v is number => typeof v === 'number') : []

    const paramSets: Record<string, Raw>[] = !hasParams ? [{}] : [
      ...(defaultP ? [{...defaultP}] : []),
      ...Array.from({length: 4}, () => Object.fromEntries(meta.params.map(([n, , k]) => [n, sampleKind(k, rand, 12, hints)]))).filter(cand => {
        const enc = tryCall(() => fRule.encodeParams(cand as never))
        return enc.ok && (!fMachine.pre || evalC(fMachine.pre, enc.val, {scalars: {}, maps: {}}, fMachine))
      }),
    ]
    if (!paramSets.length) paramSets.push(Object.fromEntries(meta.params.map(([n, k]) => [n, k.empty()])))

    const finInputs = finiteRecord(meta.inputs.map(([n, , k]) => [n, k]), 4096)
    const checkOne = (args: Record<string, Raw>, params: Record<string, Raw>): string | undefined => {
      const want = tryCall(() => {
        const ps = fRule.encodeParams(params as never)
        if (fMachine.pre && !evalC(fMachine.pre, ps, {scalars: {}, maps: {}}, fMachine)) throw new Error('pre')
        const st0 = interp.init(ps), inp = fRule.encodeInput(args as never, params as never)
        if (!ruleAllowed(fMachine, interp, ps, st0, inp)) throw new Error('assume')
        const st1 = fRule.decode(interp.step(ps, st0, inp))
        return Object.fromEntries(meta.outputs.map(([n]) => [n, st1[`out.${n}`]!]))
      })
      const got = tryCall(() => (hasParams ? fn(args, params) : fn(args)))
      checked++
      if (want.ok !== got.ok) {
        return `at args=${JSON.stringify(args)}, params=${JSON.stringify(params)}: ${want.ok ? `interpreter returned ${JSON.stringify(want.val)}, emitted threw (${(got as {err: string}).err})` : `interpreter refused (${(want as {err: string}).err}), emitted returned ${JSON.stringify((got as {val: unknown}).val)}`}`
      }
      if (!want.ok || !got.ok) { throwsMatched++; return undefined }
      return deepEq(got.val, want.val) ? undefined : `at args=${JSON.stringify(args)}, params=${JSON.stringify(params)}: emitted ${JSON.stringify(got.val)} !== interpreter ${JSON.stringify(want.val)}`
    }

    const trials = opts.trials ?? 250
    for (const p of paramSets) {
      const draws = finInputs ?? Array.from({length: trials}, () => Object.fromEntries(meta.inputs.map(([n, , k]) => [n, sampleKind(k, rand, 20, hints)])))
      for (const args of draws) { const diff = checkOne(args, p); if (diff) return fail1(diff) }
      for (const [n, , k] of meta.inputs) {
        const base = Object.fromEntries(meta.inputs.map(([fn0, fk0]) => [fn0, fk0.empty()]))
        const probes: readonly Raw[] = k.kind === 'decimal' ? DEC_PROBES : k.kind === 'nat' ? [-1, 1.5, ...(k.max !== undefined ? [k.max + 1] : [])] : []
        for (const probe of probes) { const diff = checkOne({...base, [n]: probe}, p); if (diff) return fail1(diff) }
      }
    }
    return {ok: true, exit: 0, checked, exhaustive: !!finInputs && (!hasParams || !!finiteRecord(meta.params.map(([n, , k]) => [n, k]), 64)), throwsMatched}
  }

  if (resolved.kind === 'rule' || resolved.kind === 'chart') {
    const r = resolved.kind === 'chart' ? resolved.chart.rule : resolved.rule
    const initFn = mod.init as ((p: Record<string, Raw>) => Record<string, unknown>) | undefined
    const stepFn = mod.step as ((p: Record<string, Raw>, s: Record<string, unknown>, i: Record<string, unknown>) => Record<string, unknown>) | undefined
    if (typeof initFn !== 'function' || typeof stepFn !== 'function') {
      return {ok: false, exit: 2, checked: 0, exhaustive: false, throwsMatched: 0, mismatch: 'emitted module missing exported init/step functions'}
    }
    const meta = inspectRuleMeta(r), m = r.machine, interp = r.interpreter({compileHelpers: true})
    const sumNames = Object.keys(m.sums ?? {}).filter(sn => !meta.state.some(([n]) => n === sn))
    const compareState = (stE: Record<string, unknown>, stI: ReturnType<typeof interp.init>, keysTouched: Set<number>): string | undefined => {
      const dec = r.decode(stI)
      for (const [n] of meta.state) if (!deepEq(stE[n], dec[n])) return `state.${n}: emitted ${JSON.stringify(stE[n])} !== interpreter ${JSON.stringify(dec[n])}`
      for (const sn of sumNames) if (!deepEq(stE[sn], stI.scalars[sn])) return `state.${sn}: emitted ${JSON.stringify(stE[sn])} !== interpreter ${JSON.stringify(stI.scalars[sn])}`
      for (const [mapName, dflt, cellKind, cellInit] of meta.maps) {
        const emMap = stE[mapName] as Map<number, unknown>
        const emDef = Object.hasOwn(stE, `${mapName}_default`) ? stE[`${mapName}_default`] : (cellKind ? (cellInit ?? emptyVal(cellKind)) : dflt)
        const decMap = (cellKind ? dec[mapName] : undefined) as Record<string, unknown> | undefined
        const intDef = cellKind
          ? (meta.maps.find(([mn]) => mn === mapName)?.[3] ?? emptyVal(cellKind))
          : (stI.defaults?.[mapName] ?? dflt)
        const allKeys = new Set<number>([...keysTouched, ...emMap.keys(), ...(stI.maps[mapName]?.keys() ?? []), 0, 1, ...Object.keys(decMap ?? {}).map(Number)])
        for (const k of allKeys) {
          const got = emMap.get(k) ?? emDef
          let want: unknown
          if (cellKind) {
            if (decMap && Object.hasOwn(decMap, String(k))) want = decMap[String(k)]
            else {
              // Decode default cell from interpreter's defaults if broadcast-updated
              const cellRef = r.kindsOfCells().find(([cn]) => cn === mapName)?.[1]
              want = cellRef
                ? cellRef.decode(mapName, Object.fromEntries(cellRef.vars(mapName).map(part => [part, stI.maps[part]?.get(k) ?? stI.defaults?.[part] ?? m.maps?.[part] ?? 0])))
                : intDef
            }
          } else {
            want = stI.maps[mapName]?.get(k) ?? stI.defaults?.[mapName] ?? dflt
          }
          if (!deepEq(got, want)) return `state.${mapName}[${k}]: emitted ${JSON.stringify(got)} !== interpreter ${JSON.stringify(want)}`
        }
      }
      for (const listName of meta.lists) {
        const len = stI.scalars[`${listName}_len`] ?? 0
        const want = Array.from({length: len}, (_, i) => stI.maps[listName]?.get(i) ?? 0)
        if (!deepEq(stE[listName], want)) return `state.${listName}: emitted ${JSON.stringify(stE[listName])} !== interpreter ${JSON.stringify(want)}`
      }
      for (const [itemName] of meta.items) if (!deepEq(stE[itemName], dec[itemName])) return `state.${itemName}: emitted ${JSON.stringify(stE[itemName])} !== interpreter ${JSON.stringify(dec[itemName])}`
      for (const nt of meta.nodes) if (!deepEq(stE[nt.name], dec[nt.name])) return `state.${nt.name}: emitted ${JSON.stringify(stE[nt.name])} !== interpreter ${JSON.stringify(dec[nt.name])}`
      return undefined
    }

    for (let runIdx = 0; runIdx < (opts.runs ?? 25); runIdx++) {
      let pRaw: Record<string, Raw> = {}, ps: Record<string, number> = {}, validP = false
      for (let attempt = 0; attempt < 40; attempt++) {
        pRaw = Object.fromEntries(meta.params.map(([n, , k]) => [n, sampleKind(k, rand, 12, [])]))
        const enc = tryCall(() => r.encodeParams(pRaw as never))
        if (enc.ok && (!m.pre || evalC(m.pre, enc.val, {scalars: {}, maps: {}}, m))) { ps = enc.val; validP = true; break }
      }
      if (!validP) continue
      let stI = interp.init(ps)
      const stE0 = tryCall(() => initFn(pRaw))
      checked++
      if (!stE0.ok) return fail1(`init(${JSON.stringify(pRaw)}) threw: ${stE0.err}`)
      let stE = stE0.val
      const keysTouched = new Set<number>([0, 1, 2])
      const initDiff = compareState(stE, stI, keysTouched)
      if (initDiff) return fail1(`init(${JSON.stringify(pRaw)}): ${initDiff}`)

      const trace: Record<string, unknown>[] = []
      let monoClock = 0
      for (let s = 0; s < (opts.steps ?? 20); s++) {
        const iRaw: Record<string, unknown> = Object.fromEntries(meta.inputs.map(([n, , k]) => {
          if (k.kind === 'nat' && (n === 't' || n === 'now' || n === r.orderedBy)) { monoClock += rand(8); return [n, monoClock] }
          return [n, sampleKind(k, rand, 15, [])]
        }))
        for (const cn of meta.carried) {
          const entries: [number, number][] = []
          const len = rand(5)
          for (let j = 0; j < len; j++) if (rand(2) === 1) entries.push([j, rand(2) === 0 ? 1 : rand(4) + 1])
          iRaw[cn] = rand(2) === 0 ? new Map(entries) : entries.map(([k]) => k)
        }
        for (const sn of meta.seqs) iRaw[sn] = Array.from({length: rand(5)}, () => rand(5))
        for (const tn of meta.seqTables) iRaw[tn] = Array.from({length: rand(4)}, () => Array.from({length: rand(4)}, () => rand(5)))
        for (const cl of meta.carriedLists) iRaw[cl.name] = Array.from({length: rand(5)}, () => sampleKind(cl.kind, rand, 8, []))
        for (const v of Object.values(iRaw)) if (typeof v === 'number' && Number.isInteger(v) && v >= 0 && v < 1000) keysTouched.add(v)
        const nextI = tryCall(() => {
          const enc = r.encodeInput(iRaw as never, pRaw as never)
          if (!ruleAllowed(m, interp, ps, stI, enc)) throw new Error('not allowed')
          return interp.step(ps, stI, enc)
        })
        const nextE = tryCall(() => stepFn(pRaw, stE, iRaw))
        checked++
        if (nextI.ok !== nextE.ok) {
          return fail1(`params=${JSON.stringify(pRaw)}, step ${s}, input=${JSON.stringify(iRaw, (_k, v) => v instanceof Map ? Object.fromEntries(v) : v)}: ${nextI.ok ? `interpreter succeeded, emitted threw (${(nextE as {err: string}).err})` : `interpreter refused (${(nextI as {err: string}).err}), emitted succeeded`}`)
        }
        if (!nextI.ok || !nextE.ok) { throwsMatched++; continue }
        stI = nextI.val; stE = nextE.val; trace.push(iRaw)
        const diff = compareState(stE, stI, keysTouched)
        if (diff) return fail1(`params=${JSON.stringify(pRaw)}, step ${s}: ${diff}`)
      }
    }
    return {ok: true, exit: 0, checked, exhaustive: false, throwsMatched}
  }

  if (resolved.kind === 'fold') {
    const f = resolved.fold
    const fn = mod[res.exportName] as ((tree: unknown, params?: Record<string, Raw>) => Record<string, number>) | undefined
    if (typeof fn !== 'function') return {ok: false, exit: 2, checked: 0, exhaustive: false, throwsMatched: 0, mismatch: `emitted fold missing exported function ${res.exportName}`}
    const meta = inspectFoldMeta(f)
    const mkTree = (d: number): unknown => {
      const own = Object.fromEntries(meta.inputs.map(([n, , k]) => [n, sampleKind(k, rand, 12, [])]))
      if (d === 0 || rand(3) === 0) return {leaf: own}
      return meta.rose
        ? {node: own, children: Array.from({length: rand(4)}, () => mkTree(d - 1))}
        : {node: own, left: mkTree(d - 1), right: mkTree(d - 1)}
    }
    for (let t = 0; t < (opts.trials ?? 120); t++) {
      const pRaw = Object.fromEntries(meta.params.map(([n, , k]) => [n, sampleKind(k, rand, 12, [])]))
      const tree = mkTree(3)
      const want = tryCall(() => f.run(tree as never, pRaw as never))
      const got = tryCall(() => (meta.params.length ? fn(tree, pRaw) : fn(tree)))
      checked++
      if (want.ok !== got.ok) return fail1(`fold trial ${t}: ${want.ok ? `interpreter returned ${JSON.stringify(want.val)}, emitted threw (${(got as {err: string}).err})` : `interpreter threw (${(want as {err: string}).err}), emitted returned ${JSON.stringify((got as {val: unknown}).val)}`}`)
      if (!want.ok || !got.ok) { throwsMatched++; continue }
      if (!deepEq(got.val, want.val)) return fail1(`fold trial ${t}: emitted ${JSON.stringify(got.val)} !== interpreter ${JSON.stringify(want.val)}`)
    }
    return {ok: true, exit: 0, checked, exhaustive: false, throwsMatched}
  }

  if (resolved.kind === 'loop') {
    const l = resolved.loop, meta = inspectLoopMeta(l), lp = meta.loop
    const initFn = mod.init as ((p: Record<string, Raw>) => Record<string, number>) | undefined
    const guardFn = mod.guard as ((p: Record<string, Raw>, s: Record<string, number>) => boolean) | undefined
    const bodyFn = mod.body as ((p: Record<string, Raw>, s: Record<string, number>, i: Record<string, Raw>) => Record<string, number>) | undefined
    const runFn = mod.run as ((p: Record<string, Raw>, xs: readonly Record<string, Raw>[]) => Record<string, number>) | undefined
    if (!initFn || !guardFn || !bodyFn || !runFn) return {ok: false, exit: 2, checked: 0, exhaustive: false, throwsMatched: 0, mismatch: 'emitted loop missing init/guard/body/run exports'}
    const emptyMachine = {name: lp.name, params: [], inputs: [], state: {}, step: {}}
    const emptySt = {scalars: {}, maps: {}}
    const encKinds = (kinds: readonly [string, {encode(n: string, raw: Raw): Record<string, number>}, KindInfo][], raw: Record<string, Raw>) =>
      Object.assign({}, ...kinds.map(([n, k]) => k.encode(n, raw[n]!))) as Record<string, number>
    for (let runIdx = 0; runIdx < (opts.runs ?? 25); runIdx++) {
      const pRaw = Object.fromEntries(meta.params.map(([n, , k]) => [n, sampleKind(k, rand, 10, [])]))
      const wantInit = tryCall(() => {
        const ps = encKinds(meta.params, pRaw)
        if (lp.pre && !evalC(lp.pre, ps, emptySt, emptyMachine)) throw new Error('pre')
        return {ps, st: Object.fromEntries(meta.state.map(sn => [sn, evalE(lp.state[sn]!, ps, emptySt, emptyMachine)]))}
      })
      const gotInit = tryCall(() => initFn(pRaw))
      checked++
      if (wantInit.ok !== gotInit.ok) return fail1(`loop init(${JSON.stringify(pRaw)}): parity mismatch`)
      if (!wantInit.ok || !gotInit.ok) { throwsMatched++; continue }
      let stI = wantInit.val.st, stE = gotInit.val
      const ps = wantInit.val.ps
      if (!deepEq(stE, stI)) return fail1(`loop init(${JSON.stringify(pRaw)}): ${JSON.stringify(stE)} !== ${JSON.stringify(stI)}`)
      const acceptedInputs: Record<string, Raw>[] = []
      for (let stepIdx = 0; stepIdx < (opts.steps ?? 20); stepIdx++) {
        const gI = evalC(lp.while, {...ps, ...stI}, emptySt, emptyMachine)
        const gE = guardFn(pRaw, stE)
        checked++
        if (gI !== gE) return fail1(`loop guard mismatch at step ${stepIdx}: emitted ${gE} !== interpreter ${gI}`)
        if (!gI) break
        const iRaw = Object.fromEntries(meta.inputs.map(([n, , k]) => [n, sampleKind(k, rand, 10, [])]))
        const nextI = tryCall(() => {
          const inp = encKinds(meta.inputs, iRaw)
          const env = {...ps, ...stI, ...inp}
          if (lp.assume && !evalC(lp.assume, env, emptySt, emptyMachine)) throw new Error('assume')
          return {...stI, ...Object.fromEntries(Object.entries(lp.body).map(([sn, e]) => [sn, evalE(e, env, emptySt, emptyMachine)]))}
        })
        const nextE = tryCall(() => bodyFn(pRaw, stE, iRaw))
        checked++
        if (nextI.ok !== nextE.ok) return fail1(`loop body parity mismatch at step ${stepIdx}`)
        if (!nextI.ok || !nextE.ok) { throwsMatched++; continue }
        stI = nextI.val; stE = nextE.val; acceptedInputs.push(iRaw)
        if (!deepEq(stE, stI)) return fail1(`loop body step ${stepIdx}: ${JSON.stringify(stE)} !== ${JSON.stringify(stI)}`)
      }
      const runOut = runFn(pRaw, acceptedInputs)
      checked++
      if (!deepEq(runOut, stI)) return fail1(`loop run(): ${JSON.stringify(runOut)} !== ${JSON.stringify(stI)}`)
    }
    return {ok: true, exit: 0, checked, exhaustive: false, throwsMatched}
  }

  if (resolved.kind !== 'ratRule') return unreachable(resolved)

  // RatRule differential verification against interpretQ
  const meta = inspectRatRule(resolved.ratRule), qInterp = interpretQ(meta.machine)
  const toRat = mod.toRat as ((x: unknown) => readonly [bigint, bigint]) | undefined
  const formatRat = mod.formatRat as ((r: readonly [bigint, bigint]) => string) | undefined
  const initFn = mod.init as ((p: Record<string, readonly [bigint, bigint]>) => Record<string, readonly [bigint, bigint]>) | undefined
  const allowedFn = mod.allowed as ((p: Record<string, readonly [bigint, bigint]>, s: Record<string, readonly [bigint, bigint]>, i: Record<string, readonly [bigint, bigint]>) => boolean) | undefined
  const stepFn = mod.step as ((p: Record<string, readonly [bigint, bigint]>, s: Record<string, readonly [bigint, bigint]>, i: Record<string, readonly [bigint, bigint]>) => Record<string, readonly [bigint, bigint]>) | undefined
  if (!toRat || !formatRat || !initFn || !allowedFn || !stepFn) {
    return {ok: false, exit: 2, checked: 0, exhaustive: false, throwsMatched: 0, mismatch: 'emitted RatRule module missing required exports'}
  }
  const ratNonneg = ['0', '0.1', '1/3', '0.25', '0.4', '0.5', '2/3', '1', '2', '12.50', '999999.99']
  const ratAny = ['-2', '-1/3', '0', '0.1', '1/3', '0.5', '1', '2', '3']
  const pickRat = (nonneg: boolean) => { const pool = nonneg ? ratNonneg : ratAny; return pool[rand(pool.length)]! }
  for (let runIdx = 0; runIdx < (opts.runs ?? 25); runIdx++) {
    const pRaw = Object.fromEntries(meta.params.map(([n, k]) => [n, pickRat(!!k.nonneg)]))
    const pQ = Object.fromEntries(Object.entries(pRaw).map(([n, v]) => [n, qparse(v)]))
    const pE = Object.fromEntries(Object.entries(pRaw).map(([n, v]) => [n, toRat(v)]))
    let stQ = qInterp.init(pQ), stE = initFn(pE)
    checked++
    for (const s of meta.state) if (formatRat(stE[s]!) !== qshow(stQ[s]!)) return fail1(`RatRule init(${JSON.stringify(pRaw)}).${s}: emitted ${formatRat(stE[s]!)} !== interpreter ${qshow(stQ[s]!)}`)
    for (let stepIdx = 0; stepIdx < (opts.steps ?? 15); stepIdx++) {
      const iRaw = Object.fromEntries(meta.inputs.map(([n, k]) => [n, pickRat(!!k.nonneg)]))
      const iQ = Object.fromEntries(Object.entries(iRaw).map(([n, v]) => [n, qparse(v)]))
      const iE = Object.fromEntries(Object.entries(iRaw).map(([n, v]) => [n, toRat(v)]))
      const okQ = qInterp.allowed(pQ, stQ, iQ), okE = allowedFn(pE, stE, iE)
      checked++
      if (okQ !== okE) return fail1(`RatRule allowed mismatch at ${JSON.stringify(iRaw)}: emitted ${okE} !== interpreter ${okQ}`)
      if (!okQ) {
        if (tryCall(() => stepFn(pE, stE, iE)).ok) return fail1(`RatRule step did not refuse disallowed input ${JSON.stringify(iRaw)}`)
        throwsMatched++; continue
      }
      stQ = qInterp.step(pQ, stQ, iQ); stE = stepFn(pE, stE, iE)
      for (const s of meta.state) if (formatRat(stE[s]!) !== qshow(stQ[s]!)) return fail1(`RatRule step ${stepIdx} (${JSON.stringify(iRaw)}).${s}: emitted ${formatRat(stE[s]!)} !== interpreter ${qshow(stQ[s]!)}`)
    }
  }
  return {ok: true, exit: 0, checked, exhaustive: false, throwsMatched}
}

export async function emitMain(argv: string[]): Promise<number> {
  const parsed = parseEmitArgs(argv)
  if (!parsed.ok) { if (parsed.help) { out(parsed.error); return 0 } err(parsed.error); return 2 }
  const opts = parsed.opts
  let resolved: ResolvedTarget, res: EmitResult
  try { ({resolved, result: res} = await resolveAndEmit(opts)) } catch (e) { err(`gdp-wired emit: ${e instanceof Error ? e.message : String(e)}`); return 2 }

  if (!res.allProven) {
    const failed = res.laws.filter(l => !(l.proven && l.checked))
    if (opts.json) out(JSON.stringify({ok: false, exit: 2, name: res.name, digest: res.digest, allProven: false, laws: res.laws}, null, 1))
    else {
      err(`gdp-wired emit: refused "${res.name}" — not all laws are proven`)
      if (res.laws.length === 0) err('  no laws were provided or registered on this target (pass --laws <export>)')
      for (const l of failed) err(`  - [${l.kind}] ${l.name}: ${l.why ?? l.goal ?? 'unproven'}`)
    }
    return 2
  }

  const outPath = opts.out ? path.resolve(proc.cwd(), opts.out) : undefined
  if (opts.check) {
    if (!outPath || !fs.existsSync(outPath)) {
      if (opts.json) out(JSON.stringify({ok: false, exit: 1, check: 'missing', out: opts.out, digest: res.digest}, null, 1))
      else err(`gdp-wired emit --check: file missing: ${opts.out ?? ''}`)
      return 1
    }
    const existing = fs.readFileSync(outPath, 'utf8')
    if (existing !== res.source) {
      const diffText = shortDiff(existing, res.source)
      if (opts.json) out(JSON.stringify({ok: false, exit: 1, check: 'diff', out: opts.out, digest: res.digest, diff: diffText}, null, 1))
      else { err(`gdp-wired emit --check: ${opts.out} is out of date`); err(diffText) }
      return 1
    }
  } else if (outPath) {
    fs.mkdirSync(path.dirname(outPath), {recursive: true})
    fs.writeFileSync(outPath, res.source)
  }

  let verifyResult: VerifyDiffResult | undefined
  if (opts.verify) {
    let verifyPath = outPath, tmpFile: string | undefined
    if (!verifyPath) {
      tmpFile = path.join(osMod.tmpdir(), `gdp-wired-emit-${proc.pid}-${res.digest.slice(7, 19)}.ts`)
      fs.writeFileSync(tmpFile, res.source)
      verifyPath = tmpFile
    }
    try { verifyResult = await verifyEmittedFile(verifyPath, resolved, res) } finally { if (tmpFile) fs.rmSync(tmpFile, {force: true}) }
    if (!verifyResult.ok) {
      if (opts.json) out(JSON.stringify({ok: false, exit: verifyResult.exit, name: res.name, digest: res.digest, verify: verifyResult}, null, 1))
      else err(`gdp-wired emit --verify: MISMATCH (${verifyResult.checked} checked): ${verifyResult.mismatch ?? 'failed'}`)
      return verifyResult.exit
    }
  }

  if (opts.json) {
    out(JSON.stringify({ok: true, exit: 0, name: res.name, kind: res.kind, version: res.version, digest: res.digest, ...(opts.out ? {out: opts.out} : {}), laws: res.laws, ...(verifyResult ? {verify: verifyResult} : {})}, null, 1))
  } else if (!outPath && !opts.check) {
    proc.stdout.write(res.source)
  } else {
    const rel = outPath ? (path.relative(proc.cwd(), outPath) || outPath) : res.name
    const vText = verifyResult ? `; verified ${verifyResult.checked} differential trials${verifyResult.exhaustive ? ' (exhaustive)' : ''} (${verifyResult.throwsMatched} error checks matched)` : ''
    out(`gdp-wired emit: ${opts.check ? 'up to date' : 'wrote'} ${rel} (${res.laws.length} proven laws, ${res.digest.slice(0, 19)}...${vText})`)
  }
  return 0
}
