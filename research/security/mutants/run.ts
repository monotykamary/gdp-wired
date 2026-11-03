import {cpSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, symlinkSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join, resolve} from 'node:path'
import {createHash} from 'node:crypto'
import {spawnSync} from 'node:child_process'
import {check, type RuleOut} from '../../../core/cli.ts'
import {interned} from '../../../core/dsl.ts'
import ts from 'typescript'
import {mutate, type Mutation} from './operators.ts'
import {replayEffect} from './replay_effect.ts'
import {replayClass, replayIsolation, type Replay} from './replay.ts'

export const fixtures = readdirSync(join(import.meta.dir, 'fixtures')).sort()
export const budgetMs = 8000
const sha = (s: string) => createHash('sha256').update(s).digest('hex')
type Claim = RuleOut['laws'][number] & {entry?: string, concreteOwner?: string | number}
export type Side = {sha256: string, exit: number, fullyRead: boolean, claims: Claim[], rules: {entry?: string, ok: boolean, checked?: string, refusals: RuleOut['refusals'], env?: string[]}[], proposals: {count: number, broken: number, allReviewRequired: boolean}}
export type MutantResult = Omit<Mutation, 'source'> & {side: Side, detected: boolean, replays: {law: string, expr: string, entry?: string, mutant: Replay, parent: Replay}[]}
export type Measurement = {fixture: string, file: string, configSha256?: string, budgetMs: number, harness: Record<string, string>, runtime: string, baseline: Side, mutants: MutantResult[]}
export function harnessHashes(): Record<string, string> {
  return Object.fromEntries(['operators.ts', 'run.ts', 'replay.ts', 'replay_race.py', 'replay_effect.ts'].map(f => [f, sha(readFileSync(join(import.meta.dir, f), 'utf8'))]))
}
function concreteOwner(file: string, law: RuleOut['laws'][number]): string | number | undefined {
  const name = /^isolated by ([A-Za-z_]\w*) seeing result$/.exec(law.expr)?.[1]
  const encoded = /^B is (\d+) /.exec(law.run?.[0] ?? '')?.[1]
  if (!name || encoded === undefined || !file.endsWith('.ts')) return undefined
  const sf = ts.createSourceFile(file, readFileSync(file, 'utf8'), ts.ScriptTarget.Latest, true)
  const kinds = new Set<ts.SyntaxKind>()
  const visit = (n: ts.Node) => {
    if (ts.isParameter(n) && ts.isIdentifier(n.name) && n.name.text === name && n.type) kinds.add(n.type.kind)
    ts.forEachChild(n, visit)
  }
  visit(sf)
  if (kinds.size !== 1) return undefined
  if (kinds.has(ts.SyntaxKind.NumberKeyword)) return Number(encoded)
  if (kinds.has(ts.SyntaxKind.StringKeyword)) return interned().find(([, id]) => id === Number(encoded))?.[0]
  return undefined
}

async function inspect(file: string): Promise<Side> {
  const result = await check([file], {ms: budgetMs, propose: false, security: true})
  const proposals = result.rules.flatMap(r => r.security ?? [])
  return {sha256: sha(readFileSync(file, 'utf8')), exit: result.exit,
    fullyRead: result.rules.length > 0 && result.rules.every(r => r.ok && !!r.checked && r.laws.every(l => l.verdict !== 'not read')),
    claims: result.rules.flatMap(r => r.laws.map(l => ({...l, entry: r.entry, where: l.where?.replace(file, '<source>'), ...(l.kind === 'two runs' ? {concreteOwner: concreteOwner(file, l)} : {})}))),
    rules: result.rules.map(r => ({entry: r.entry, ok: r.ok, checked: r.checked, refusals: r.refusals, env: r.env})),
    proposals: {count: proposals.length, broken: proposals.filter(p => p.verdict === 'broken').length, allReviewRequired: proposals.every(p => p.review === 'required')}}
}
export function replayPython(file: string, law: Claim, dir: string): Replay {
  const request = join(dir, 'replay.json')
  writeFileSync(request, JSON.stringify({file, entry: law.entry, expr: law.expr, run: law.run}))
  const p = spawnSync('python3', [join(import.meta.dir, 'replay_race.py'), request], {encoding: 'utf8', timeout: 30_000})
  if (p.status !== 0) return {ok: false, broken: false, steps: [], why: p.error?.message ?? p.stderr ?? 'replay process failed'}
  return JSON.parse(p.stdout) as Replay
}

export async function replaySource(file: string, law: Claim, dir: string, parent = false): Promise<Replay> {
  if (file.endsWith('.py')) return replayPython(file, law, dir)
  if (/from\s+['"]effect['"]/.test(readFileSync(file, 'utf8'))) return replayEffect(file, law.entry!, law.expr, law.run!, dir, parent)
  if (law.kind === 'two runs') return replayIsolation(file, law.entry!, law.expr, law.run!, law.concreteOwner)
  return replayClass(file, law.entry!, law.expr, law.run!, law.kind === 'step' ? Number(law.where?.split(':').at(-1)) : undefined)
}

export async function measure(fixture: string): Promise<Measurement> {
  if (!fixtures.includes(fixture)) throw new Error('only the owned fixture corpus is accepted')
  const original = join(import.meta.dir, 'fixtures', fixture)
  const filename = readdirSync(original).find(f => /^module\.(ts|py)$/.test(f))!
  const language = filename.endsWith('.ts') ? 'ts' : 'py'
  const source = readFileSync(join(original, filename), 'utf8')
  const root = mkdtempSync(join(tmpdir(), 'security-mutants-'))
  symlinkSync(resolve(import.meta.dir, '../../..', 'node_modules'), join(root, 'node_modules'), 'dir')
  try {
    const make = (id: string, code: string) => {
      const dir = join(root, id)
      mkdirSync(dir)
      for (const f of readdirSync(original)) cpSync(join(original, f), join(dir, f))
      const path = join(dir, filename)
      writeFileSync(path, code)
      return {dir, path}
    }
    const parent = make('baseline', source), baseline = await inspect(parent.path)
    const mutants: MutantResult[] = []
    for (const mutation of mutate(source, language)) {
      const target = make(mutation.id, mutation.source), side = await inspect(target.path)
      const replays: MutantResult['replays'] = []
      for (const law of side.claims.filter(l => l.verdict === 'broken' && l.run?.length && l.entry)) {
        const counterpart = baseline.claims.find(l => l.entry === law.entry && l.name === law.name && l.expr === law.expr)
        if (!counterpart || !['proven', 'unknown'].includes(counterpart.verdict)) continue
        const mutant = await replaySource(target.path, law, target.dir)
        const clean = await replaySource(parent.path, {...counterpart, run: law.run, concreteOwner: law.concreteOwner}, parent.dir, true)
        replays.push({law: law.name, expr: law.expr, entry: law.entry, mutant, parent: clean})
      }
      const detected = admit(baseline, side, replays)
      const {source: _source, ...change} = mutation
      mutants.push({...change, side, detected, replays})
    }
    const config = readdirSync(original).includes('gdp.toml') ? sha(readFileSync(join(original, 'gdp.toml'), 'utf8')) : undefined
    return {fixture, file: filename, configSha256: config, budgetMs, harness: harnessHashes(), runtime: `Bun ${process.versions.bun ?? 'unknown'}`, baseline, mutants}
  } finally { rmSync(root, {recursive: true, force: true}) }
}

export function admit(baseline: Side, side: Side, replays: MutantResult['replays']): boolean {
  if (!baseline.fullyRead || !side.fullyRead || baseline.claims.some(l => l.verdict === 'broken')) return false
  return replays.some(r => r.mutant.ok && r.mutant.broken && r.mutant.steps.length > 0 && r.parent.ok && !r.parent.broken && r.parent.steps.length > 0
    && side.claims.some(l => l.entry === r.entry && l.name === r.law && l.expr === r.expr && l.verdict === 'broken' && !!l.run?.length)
    && baseline.claims.some(l => l.entry === r.entry && l.name === r.law && l.expr === r.expr && ['proven', 'unknown'].includes(l.verdict)))
}

export function summarize(rows: Measurement[]) {
  const mutants = rows.flatMap(r => r.mutants), sides = rows.flatMap(r => [r.baseline, ...r.mutants.map(m => m.side)])
  return {baselines: rows.length, baselineRefuted: rows.filter(r => r.baseline.claims.some(l => l.verdict === 'broken')).length,
    baselineProven: rows.filter(r => r.baseline.claims.length > 0 && r.baseline.claims.every(l => l.verdict === 'proven')).length,
    mutants: mutants.length, detected: mutants.filter(m => m.detected).length,
    fullyRead: sides.filter(s => s.fullyRead).length, sides: sides.length,
    reviewRequired: sides.every(s => s.proposals.allReviewRequired)}
}

if (import.meta.main) {
  const requested = process.argv.slice(2)
  for (const fixture of requested.length ? requested : fixtures) {
    const row = await measure(fixture)
    console.log('MUTATION_RESULT ' + JSON.stringify(row, (_k, v: unknown) => v instanceof Map ? {$map: [...v]} : v))
    console.error(JSON.stringify(summarize([row])))
  }
}
