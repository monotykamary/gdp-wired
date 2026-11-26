// CLI for `gdp-wired emit <module>#<export> [--out <file.ts>] [--check] [--verify] [--laws <export>] [--step-laws <export>] [--from any] [--ms 10000] [--json]`.
// Exit codes:
//   0: emitted (and matched under --check, and verified under --verify)
//   1: --check drift detected, or --verify refuted a broken law
//   2: unproven rule/law, bad arguments, missing export, or --verify could not check / reader refused
import {
  type Decision,
  type EmitBundle,
  type EmitResult,
  Fun,
  Rule,
  Chart,
  emitChart,
  emitFun,
  emitRatRule,
  emitRule,
} from './dsl.ts'
import {type RatLaw, RatRule} from './rationals.ts'
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
  --verify            Re-check the emitted file through the TypeScript reader against its emitted gdp: law comments
  --laws <export>     Export name in <module> holding the laws array (or function returning it)
  --step-laws <exp>   Export name in <module> holding the step laws array (or function returning it)
  --name <ident>      Override generated function/class name
  --from any          Prove invariants from every state allowed by the laws
  --ms <ms>           Proof search budget in milliseconds (default 10000)
  --json              Output structured JSON result

Exit codes: 0 ok; 1 --check diff or --verify broken law; 2 unproven rule/law, error, or reader refusal.`

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

export async function emitTarget(opts: EmitCliOptions): Promise<EmitResult> {
  const hash = opts.target.lastIndexOf('#')
  if (hash <= 0 || hash === opts.target.length - 1) {
    throw new Error(`expected <module>#<export>, got "${opts.target}"`)
  }
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
    return emitRule(target as never, {
      ...(laws ? {laws} : {}),
      ...(stepLaws ? {stepLaws} : {}),
      ...(opts.name ? {name: opts.name} : {}),
      ...(opts.from ? {from: opts.from} : {}),
      ...(opts.ms !== undefined ? {ms: opts.ms} : {}),
      allowUnproven: true,
    })
  }
  if (target instanceof Fun) {
    const laws = opts.laws ? resolveLawExport<Decision>(mod, opts.laws, target) : undefined
    return emitFun(target as never, {
      ...(laws ? {laws} : {}),
      ...(opts.name ? {name: opts.name} : {}),
      ...(opts.ms !== undefined ? {ms: opts.ms} : {}),
      allowUnproven: true,
    })
  }
  if (target instanceof RatRule) {
    const laws = opts.laws ? resolveLawExport<RatLaw<string, string>>(mod, opts.laws, target) : undefined
    return emitRatRule(target as never, {
      ...(laws ? {laws} : {}),
      ...(opts.name ? {name: opts.name} : {}),
      ...(opts.ms !== undefined ? {ms: opts.ms} : {}),
      allowUnproven: true,
    })
  }
  if (target instanceof Chart) {
    const laws = opts.laws ? resolveLawExport<Law>(mod, opts.laws, target) : undefined
    const stepLaws = opts.stepLaws ? resolveLawExport<StepLaw>(mod, opts.stepLaws, target) : undefined
    return emitChart(target as never, {
      ...(laws ? {laws} : {}),
      ...(stepLaws ? {stepLaws} : {}),
      ...(opts.name ? {name: opts.name} : {}),
      ...(opts.from ? {from: opts.from} : {}),
      ...(opts.ms !== undefined ? {ms: opts.ms} : {}),
      allowUnproven: true,
    })
  }
  if (isEmitBundle(target)) {
    if ('rule' in target) {
      const laws = opts.laws ? resolveLawExport<Law>(mod, opts.laws, target.rule) : target.laws
      const stepLaws = opts.stepLaws ? resolveLawExport<StepLaw>(mod, opts.stepLaws, target.rule) : target.stepLaws
      return emitRule(target.rule, {
        ...(laws ? {laws} : {}),
        ...(stepLaws ? {stepLaws} : {}),
        ...(opts.name ?? target.name ? {name: opts.name ?? target.name} : {}),
        ...(opts.from ?? target.from ? {from: opts.from ?? target.from} : {}),
        ...(opts.ms ?? target.ms !== undefined ? {ms: opts.ms ?? target.ms} : {}),
        allowUnproven: true,
      })
    }
    if ('fun' in target) {
      const laws = opts.laws ? resolveLawExport<Decision>(mod, opts.laws, target.fun) : target.laws
      return emitFun(target.fun, {
        ...(laws ? {laws} : {}),
        ...(target.defaultParams ? {defaultParams: target.defaultParams} : {}),
        ...(opts.name ?? target.name ? {name: opts.name ?? target.name} : {}),
        ...(opts.ms ?? target.ms !== undefined ? {ms: opts.ms ?? target.ms} : {}),
        allowUnproven: true,
      })
    }
    if ('ratRule' in target) {
      const laws = opts.laws ? resolveLawExport<RatLaw<string, string>>(mod, opts.laws, target.ratRule) : target.laws
      return emitRatRule(target.ratRule, {
        ...(laws ? {laws} : {}),
        ...(opts.name ?? target.name ? {name: opts.name ?? target.name} : {}),
        ...(opts.ms ?? target.ms !== undefined ? {ms: opts.ms ?? target.ms} : {}),
        allowUnproven: true,
      })
    }
    if ('chart' in target) {
      const laws = opts.laws ? resolveLawExport<Law>(mod, opts.laws, target.chart) : target.laws
      const stepLaws = opts.stepLaws ? resolveLawExport<StepLaw>(mod, opts.stepLaws, target.chart) : target.stepLaws
      return emitChart(target.chart, {
        ...(laws ? {laws} : {}),
        ...(stepLaws ? {stepLaws} : {}),
        ...(opts.name ?? target.name ? {name: opts.name ?? target.name} : {}),
        ...(opts.from ?? target.from ? {from: opts.from ?? target.from} : {}),
        ...(opts.ms ?? target.ms !== undefined ? {ms: opts.ms ?? target.ms} : {}),
        allowUnproven: true,
      })
    }
  }
  throw new Error(`export "${expName}" is not a Rule, Fun, RatRule, Chart, or EmitBundle`)
}

export type VerifyEmittedResult = {
  readonly ok: boolean
  readonly exit: 0 | 1 | 2
  readonly proven: number
  readonly broken: number
  readonly unknown: number
  readonly notRead: number
  readonly expected: number
  readonly details: readonly string[]
}

export async function verifyEmittedFile(
  filePath: string,
  res: EmitResult,
  opts: {ms?: number} = {},
): Promise<VerifyEmittedResult> {
  if (!res.verify.verifiable || !res.verify.entry) {
    return {
      ok: false,
      exit: 2,
      proven: 0,
      broken: 0,
      unknown: 0,
      notRead: 0,
      expected: res.verify.expectedLaws.length,
      details: res.verify.reasons.length ? [...res.verify.reasons] : ['emitted module is outside the TypeScript reader subset'],
    }
  }
  const {check} = await import('./cli.ts')
  const checked = await check([filePath], {
    entry: res.verify.entry,
    ...(res.verify.mode ? {mode: res.verify.mode} : {}),
    ...(res.verify.from ? {from: res.verify.from} : {}),
    propose: false,
    ms: opts.ms ?? 10_000,
  })
  const stated = checked.rules.flatMap(r => r.laws)
  const details: string[] = []
  for (const r of checked.rules) {
    if (!r.ok) {
      for (const ref of r.refusals) details.push(`reader refused (${ref.where}): ${ref.what}`)
    }
    for (const l of r.laws) {
      if (l.verdict !== 'proven') {
        details.push(`[${l.verdict}] ${l.name}${l.why ? `: ${l.why}` : ''}${l.run?.length ? ` (run: ${l.run.join(' -> ')})` : ''}`)
      }
    }
  }
  const proven = stated.filter(l => l.verdict === 'proven').length
  const broken = stated.filter(l => l.verdict === 'broken').length
  const unknown = stated.filter(l => l.verdict === 'unknown').length
  const notRead = stated.filter(l => l.verdict === 'not read').length
  const expected = res.verify.expectedLaws.length
  const allFound = stated.length === expected && checked.rules.length > 0 && checked.rules.every(r => r.ok)
  if (!allFound && details.length === 0) {
    details.push(`expected ${expected} laws in ${filePath}, reader saw ${stated.length}`)
  }
  const exit: 0 | 1 | 2 = broken > 0
    ? 1
    : (checked.exit === 0 && allFound && proven === expected ? 0 : checked.exit === 1 ? 1 : 2)
  return {ok: exit === 0, exit, proven, broken, unknown, notRead, expected, details}
}

export async function emitMain(argv: string[]): Promise<number> {
  const parsed = parseEmitArgs(argv)
  if (!parsed.ok) {
    if (parsed.help) { out(parsed.error); return 0 }
    err(parsed.error)
    return 2
  }
  const opts = parsed.opts
  let res: EmitResult
  try {
    res = await emitTarget(opts)
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
  let diffText: string | undefined

  if (opts.check) {
    if (!outPath || !fs.existsSync(outPath)) {
      diffText = `file missing: ${opts.out ?? ''}`
      if (opts.json) out(JSON.stringify({ok: false, exit: 1, check: 'missing', out: opts.out, digest: res.digest}, null, 1))
      else err(`gdp-wired emit --check: ${diffText}`)
      return 1
    }
    const existing = fs.readFileSync(outPath, 'utf8')
    if (existing !== res.source) {
      diffText = shortDiff(existing, res.source)
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

  let verifyResult: VerifyEmittedResult | undefined
  if (opts.verify) {
    let verifyPath = outPath
    let tmpFile: string | undefined
    if (!verifyPath) {
      tmpFile = path.join(osMod.tmpdir(), `gdp-wired-emit-${proc.pid}-${res.digest.slice(7, 19)}.ts`)
      fs.writeFileSync(tmpFile, res.source)
      verifyPath = tmpFile
    }
    try {
      verifyResult = await verifyEmittedFile(verifyPath, res, {ms: opts.ms})
    } finally {
      if (tmpFile) fs.rmSync(tmpFile, {force: true})
    }
    if (!verifyResult.ok) {
      if (opts.json) {
        out(JSON.stringify({ok: false, exit: verifyResult.exit, name: res.name, digest: res.digest, verify: verifyResult}, null, 1))
      } else {
        err(`gdp-wired emit --verify: failed (${verifyResult.proven}/${verifyResult.expected} proven, ${verifyResult.broken} broken, ${verifyResult.unknown} unknown, ${verifyResult.notRead} not read)`)
        for (const d of verifyResult.details) err(`  ${d}`)
      }
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
      ...(verifyResult ? {verify: verifyResult} : {verifyMeta: res.verify}),
    }, null, 1))
  } else if (!outPath && !opts.check) {
    proc.stdout.write(res.source)
  } else {
    const rel = outPath ? (path.relative(proc.cwd(), outPath) || outPath) : res.name
    const action = opts.check ? 'up to date' : 'wrote'
    const vText = verifyResult ? `; verified ${verifyResult.proven}/${verifyResult.expected} laws via TS reader` : ''
    out(`gdp-wired emit: ${action} ${rel} (${res.laws.length} proven laws, ${res.digest.slice(0, 19)}...${vText})`)
  }
  return 0
}
