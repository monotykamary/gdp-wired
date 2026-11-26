// Full 100% expressibility coverage sweep: emit + differential --verify against the interpreter on EVERY rule,
// function, rational rule, statechart, fold, and loop across:
//   1. All 21 example domains (`examples/domains/*.ts` via `examples/index.ts`)
//   2. All standalone `examples/*.ts` modules with exported models
//   3. The entire 545-law benchmark corpus (`research/realworld/corpus.ts`, `research/protocols/models.ts` duoai +
//      broken mutants, `research/protocols/ic3syn/models.ts` ic3syn + broken mutants)
//
// Usage:
//   bun research/emit/sweep.ts [--shard k/n] [--out file.json] [--runs 10] [--steps 12] [--suite examples|domains|realworld|duoai|ic3syn|all]
import {mkdirSync, readdirSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join, resolve} from 'node:path'
import {
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
} from '../../core/dsl.ts'
import {RatRule} from '../../core/rationals.ts'
import {type ResolvedTarget, verifyEmittedFile} from '../../core/emit-cli.ts'
import {domains} from '../../examples/index.ts'
import {corpus} from '../realworld/corpus.ts'
import {decisionInput, jointSpec} from '../realworld/lib.ts'
import {cuts as duoaiCuts, protocols as duoaiProtocols} from '../protocols/models.ts'
import {protocols as ic3synProtocols} from '../protocols/ic3syn/models.ts'

type SweepEntry = {
  readonly suite: 'domains' | 'examples' | 'realworld' | 'duoai' | 'duoai-mutant' | 'ic3syn' | 'ic3syn-mutant'
  readonly id: string
  readonly target: ResolvedTarget
  readonly lawCount?: number
}

type SweepResult = {
  readonly suite: SweepEntry['suite']
  readonly id: string
  readonly kind: ResolvedTarget['kind']
  readonly lawCount: number
  readonly ok: boolean
  readonly stage: 'ok' | 'emit' | 'verify' | 'interpreter'
  readonly checked: number
  readonly throwsMatched: number
  readonly ms: number
  readonly error?: string
}

const STANDALONE_EXAMPLES: readonly string[] = [
  'abstract.ts', 'arith.ts', 'charts.ts', 'composition.ts', 'cycles.ts', 'cyclic.ts',
  'data.ts', 'datatypes.ts', 'discover.ts', 'effect-bank.ts', 'effect-pool.ts',
  'effect-queue.ts', 'effect-quota.ts', 'effect-retry-policy.ts', 'effect-retry.ts',
  'effect-stm.ts', 'effect.ts', 'exists.ts', 'folds.ts', 'functions.ts', 'gdp.ts',
  'groups.ts', 'infer.ts', 'invoices.ts', 'lemmas.ts', 'lists.ts', 'liveness.ts',
  'model-proof.ts', 'nonterm.ts', 'orderbook.ts', 'pairs.ts', 'quantifiers.ts',
  'rationals.ts', 'review-routing.ts', 'scopes.ts', 'sets.ts', 'sizes.ts', 'trees.ts',
  'wide.ts', 'xstate-mbt.ts', 'xstate.ts',
]

function targetOf(v: unknown): ResolvedTarget | undefined {
  if (v instanceof Rule) return {kind: 'rule', rule: v}
  if (v instanceof Fun) return {kind: 'fun', fun: v}
  if (v instanceof RatRule) return {kind: 'ratRule', ratRule: v}
  if (v instanceof Chart) return {kind: 'chart', chart: v}
  if (v instanceof FoldRule || v instanceof RoseFold) return {kind: 'fold', fold: v}
  if (v instanceof LoopRule) return {kind: 'loop', loop: v}
  return undefined
}

async function collectAll(suiteFilter: string): Promise<SweepEntry[]> {
  const entries: SweepEntry[] = []
  const want = (s: string) => suiteFilter === 'all' || suiteFilter.split(',').includes(s)

  if (want('domains')) {
    for (const d of domains) {
      for (const c of d.cases) {
        if (c.kind === 'rule') {
          entries.push({suite: 'domains', id: `${d.domain}/${c.name}`, target: {kind: 'rule', rule: c.rule}, lawCount: c.laws.length + (c.steps?.length ?? 0)})
          for (const b of c.broken) {
            entries.push({suite: 'domains', id: `${d.domain}/${c.name}#broken:${b.name}`, target: {kind: 'rule', rule: b.rule}, lawCount: b.laws.length})
          }
        } else if (c.kind === 'decisions') {
          const seen = new Set<object>()
          c.decisions.forEach((dec, idx) => {
            if (!seen.has(dec.rule)) {
              seen.add(dec.rule)
              entries.push({suite: 'domains', id: `${d.domain}/${c.name}#dec${idx}`, target: {kind: 'rule', rule: dec.rule}, lawCount: 1})
            }
          })
          c.broken.forEach((b, idx) => {
            if (!seen.has(b.decision.rule)) {
              seen.add(b.decision.rule)
              entries.push({suite: 'domains', id: `${d.domain}/${c.name}#broken-dec${idx}:${b.name}`, target: {kind: 'rule', rule: b.decision.rule}, lawCount: 1})
            }
          })
        } else {
          entries.push({suite: 'domains', id: `${d.domain}/${c.name}`, target: {kind: 'loop', loop: c.loop}, lawCount: c.laws.length})
          for (const b of c.broken) {
            entries.push({suite: 'domains', id: `${d.domain}/${c.name}#broken:${b.name}`, target: {kind: 'loop', loop: b.loop}, lawCount: b.laws.length})
          }
        }
      }
    }
  }

  if (want('examples')) {
    const exDir = resolve(import.meta.dir, '../../examples')
    const present = new Set(readdirSync(exDir))
    for (const file of STANDALONE_EXAMPLES) {
      if (!present.has(file)) continue
      const mod = await import(join(exDir, file)) as Record<string, unknown>
      const seen = new Set<object>()
      for (const [exp, val] of Object.entries(mod)) {
        const direct = targetOf(val)
        if (direct && !seen.has(val as object)) {
          seen.add(val as object)
          entries.push({suite: 'examples', id: `${file}#${exp}`, target: direct, lawCount: 1})
          continue
        }
        // Zero-arg factory functions returning a Rule/Fun/RatRule/Chart/FoldRule/RoseFold/LoopRule
        if (typeof val === 'function' && val.length === 0 && !/Laws|Steps|Items|Test|Check|Run|Compare|Demo|Main|Bug|make/i.test(exp)) {
          try {
            const produced = (val as () => unknown)()
            const t = targetOf(produced)
            if (t && !seen.has(produced as object)) {
              seen.add(produced as object)
              entries.push({suite: 'examples', id: `${file}#${exp}()`, target: t, lawCount: 1})
            }
          } catch {
            // Skip helper functions that expect options/state despite length === 0
          }
        }
      }
    }
  }

  if (want('realworld')) {
    for (const it of corpus) {
      const byRule = new Map<object, {rule: Rule<Record<string, never>>, laws: number}>()
      for (const law of it.laws) {
        const spec = jointSpec(law)
        const r = spec?.rule ?? law.live?.r ?? decisionInput(law)?.rule
        if (!r) continue
        const cur = byRule.get(r)
        if (cur) cur.laws++
        else byRule.set(r, {rule: r as never, laws: 1})
      }
      let idx = 0
      for (const {rule: r, laws} of byRule.values()) {
        entries.push({suite: 'realworld', id: byRule.size === 1 ? it.id : `${it.id}#${idx++}`, target: {kind: 'rule', rule: r}, lawCount: laws})
      }
    }
  }

  if (want('duoai')) {
    for (const p of [...duoaiProtocols, ...duoaiCuts]) {
      const r = p.make()
      entries.push({suite: 'duoai', id: p.id, target: {kind: 'rule', rule: r}, lawCount: p.laws(r).length})
    }
  }
  if (want('duoai-mutant')) {
    for (const p of duoaiProtocols) {
      const bad = p.make(p.bug)
      entries.push({suite: 'duoai-mutant', id: `${p.id}#mutant`, target: {kind: 'rule', rule: bad}, lawCount: p.laws(bad).length})
    }
  }

  if (want('ic3syn')) {
    for (const p of ic3synProtocols) {
      const r = p.make()
      entries.push({suite: 'ic3syn', id: p.id, target: {kind: 'rule', rule: r}, lawCount: p.laws(r).length})
    }
  }
  if (want('ic3syn-mutant')) {
    for (const p of ic3synProtocols) {
      const bad = p.make(p.bug)
      entries.push({suite: 'ic3syn-mutant', id: `${p.id}#mutant`, target: {kind: 'rule', rule: bad}, lawCount: p.laws(bad).length})
    }
  }

  return entries
}

function arg(name: string): string | undefined {
  const i = process.argv.indexOf(`--${name}`)
  return i >= 0 ? process.argv[i + 1] : undefined
}

const suiteFilter = arg('suite') ?? 'all'
const runs = Number(arg('runs') ?? 10)
const steps = Number(arg('steps') ?? 12)
const outPath = arg('out') ?? (process.env.SUPERCOMPUTER_OUTPUT_DIR ? join(process.env.SUPERCOMPUTER_OUTPUT_DIR, 'sweep-receipt.json') : undefined)
const shardSpec = arg('shard')

const allEntries = await collectAll(suiteFilter)
let entries = allEntries
if (shardSpec) {
  const [kStr, nStr] = shardSpec.split('/')
  const k = Number(kStr), n = Number(nStr)
  if (!Number.isInteger(k) || !Number.isInteger(n) || k < 1 || k > n) {
    console.error(`invalid --shard ${shardSpec}; expected k/n with 1 <= k <= n`)
    process.exit(2)
  }
  entries = allEntries.filter((_, i) => i % n === k - 1)
}

const workBase = arg('work-dir') ?? tmpdir()
const workDir = join(workBase, `gdp-wired-sweep-${process.pid}-${Date.now()}`)
mkdirSync(workDir, {recursive: true})

const results: SweepResult[] = []
let seq = 0
try {
  for (const entry of entries) {
    const t0 = performance.now()
    const lawCount = entry.lawCount ?? 1
    // First check whether the interpreter itself can construct/run the machine.
    let res
    try {
      const t = entry.target
      res =
        t.kind === 'rule' ? emitRule(t.rule, {allowUnproven: true})
        : t.kind === 'fun' ? emitFun(t.fun, {allowUnproven: true})
        : t.kind === 'ratRule' ? emitRatRule(t.ratRule, {allowUnproven: true})
        : t.kind === 'chart' ? emitChart(t.chart, {allowUnproven: true})
        : t.kind === 'fold' ? emitFold(t.fold, {allowUnproven: true})
        : emitLoop(t.loop, {allowUnproven: true})
    } catch (e) {
      results.push({
        suite: entry.suite, id: entry.id, kind: entry.target.kind, lawCount,
        ok: false, stage: 'emit', checked: 0, throwsMatched: 0,
        ms: Math.round(performance.now() - t0),
        error: e instanceof Error ? e.message : String(e),
      })
      continue
    }

    const filePath = join(workDir, `m-${++seq}.ts`)
    writeFileSync(filePath, res.source)
    try {
      const v = await verifyEmittedFile(filePath, entry.target, res, {runs, steps, trials: Math.max(40, runs * steps)})
      results.push({
        suite: entry.suite, id: entry.id, kind: entry.target.kind, lawCount,
        ok: v.ok, stage: v.ok ? 'ok' : 'verify', checked: v.checked, throwsMatched: v.throwsMatched,
        ms: Math.round(performance.now() - t0),
        ...(v.mismatch ? {error: v.mismatch} : {}),
      })
    } catch (e) {
      results.push({
        suite: entry.suite, id: entry.id, kind: entry.target.kind, lawCount,
        ok: false, stage: 'verify', checked: 0, throwsMatched: 0,
        ms: Math.round(performance.now() - t0),
        error: e instanceof Error ? e.message : String(e),
      })
    } finally {
      rmSync(filePath, {force: true})
    }
  }
} finally {
  rmSync(workDir, {recursive: true, force: true})
}

const bySuite: Record<string, {total: number, ok: number, emitFail: number, verifyFail: number, laws: number, checked: number}> = {}
for (const r of results) {
  const s = (bySuite[r.suite] ??= {total: 0, ok: 0, emitFail: 0, verifyFail: 0, laws: 0, checked: 0})
  s.total++
  s.laws += r.lawCount
  s.checked += r.checked
  if (r.ok) s.ok++
  else if (r.stage === 'emit') s.emitFail++
  else s.verifyFail++
}

const failures = results.filter(r => !r.ok)
const summary = {
  shard: shardSpec ?? '1/1',
  totalDiscovered: allEntries.length,
  totalRun: results.length,
  passed: results.length - failures.length,
  failed: failures.length,
  totalChecked: results.reduce((a, r) => a + r.checked, 0),
  totalThrowsMatched: results.reduce((a, r) => a + r.throwsMatched, 0),
  bySuite,
  failures,
}

if (outPath) {
  writeFileSync(outPath, `${JSON.stringify(summary, null, 2)}\n`)
}
console.log(JSON.stringify({
  shard: summary.shard,
  totalDiscovered: summary.totalDiscovered,
  totalRun: summary.totalRun,
  passed: summary.passed,
  failed: summary.failed,
  totalChecked: summary.totalChecked,
  bySuite: summary.bySuite,
}, null, 2))
if (failures.length > 0) {
  console.error(`FAILURES (${failures.length}):`)
  for (const f of failures.slice(0, 30)) console.error(`  [${f.suite}] ${f.id} (${f.stage}): ${f.error}`)
  process.exit(1)
}
