import {cpSync, mkdtempSync, readFileSync, rmSync, writeFileSync, readdirSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {createHash, randomUUID} from 'node:crypto'
import {spawnSync} from 'node:child_process'
import {check, type RuleOut} from '../../../core/cli.ts'
import {holds} from '../mutants/replay.ts'

export type Policy = {name: string, expr: string, method?: string}
export type Case = {id: string, vendor: string, file: string, entry: string, methods: string[], properties: string[], policies: Policy[], config: string, repository: string, commit: string, upstreamPath: string, license: string, licensePath: string, dependencyPaths: Record<string, string>, files: Record<string, string>}
export const cases = JSON.parse(readFileSync(join(import.meta.dir, 'cases.json'), 'utf8')) as Case[]
export const budgetMs = 8000
export const sha = (text: string | Buffer) => createHash('sha256').update(text).digest('hex')
export type Mutation = {id: string, operator: string, method: string, startByte: number, endByte: number, before: string, after: string, source: string}
type Scope = Record<string, unknown>
export type Replay = {ok: boolean, broken: boolean, initial?: Scope, steps: {call: {method: string, args: Scope}, before: Scope, after: Scope}[], sourceSha256?: string, why?: string}
type Claim = RuleOut['laws'][number]
type Side = {sha256: string, fullyRead: boolean, exit: number, claims: Claim[], rules: {entry?: string, ok: boolean, checked?: string, refusals: RuleOut['refusals']}[]}
export type Row = {id: string, budgetMs: number, harness: Record<string, string>, provenance: Case, baseline: Side, mutants: (Omit<Mutation, 'source'> & {side: Side, detected: boolean, replays: {policy: Policy, mutant: Replay, parent: Replay}[]})[]}
export const harness = () => Object.fromEntries(['run.ts', 'source.py', 'cases.json', '../mutants/replay.ts'].map(f => [f, sha(readFileSync(join(import.meta.dir, f)))]))

export function python<T>(request: Record<string, unknown>, directory: string): T {
  const file = join(directory, `request-${randomUUID()}.json`)
  writeFileSync(file, JSON.stringify(request))
  try {
    const p = spawnSync('python3', [join(import.meta.dir, 'source.py'), file], {encoding: 'utf8', timeout: 30_000, maxBuffer: 16 * 1024 * 1024, env: {...process.env, PYTHONDONTWRITEBYTECODE: '1'}})
    if (p.status !== 0) throw new Error(p.error?.message || p.stdout || p.stderr || 'Python process failed')
    return JSON.parse(p.stdout) as T
  } finally { rmSync(file, {force: true}) }
}

export function validateVendor(c: Case) {
  const directory = join(import.meta.dir, 'vendor', c.vendor)
  const actual = readdirSync(directory, {recursive: true, withFileTypes: true}).filter(e => e.isFile()).map(e => join(e.parentPath, e.name).slice(directory.length + 1)).sort()
  if (JSON.stringify(actual) !== JSON.stringify(Object.keys(c.files).sort())) throw new Error('vendor file set changed')
  for (const [file, hash] of Object.entries(c.files)) if (sha(readFileSync(join(directory, file))) !== hash) throw new Error(`vendor hash mismatch: ${c.id}/${file}`)
}

export function prepare(c: Case, directory: string) {
  validateVendor(c)
  return python<{source: string, mutations: Mutation[]}>({action: 'prepare', file: join(import.meta.dir, 'vendor', c.vendor, c.file), case: c}, directory)
}

export function materialize(c: Case, root: string, id: string, source: string) {
  const directory = join(root, id)
  cpSync(join(import.meta.dir, 'vendor', c.vendor), directory, {recursive: true})
  writeFileSync(join(directory, 'gdp.toml'), c.config)
  const file = join(directory, c.file)
  writeFileSync(file, source)
  return {directory, file}
}

async function inspect(file: string): Promise<Side> {
  const result = await check([file], {ms: budgetMs, propose: false, security: true})
  return {sha256: sha(readFileSync(file)), exit: result.exit,
    fullyRead: result.rules.length > 0 && result.rules.every(r => r.ok && !!r.checked && r.laws.every(l => l.verdict !== 'not read')),
    claims: result.rules.flatMap(r => r.laws.map(l => ({...l, where: l.where?.replace(file, '<source>')}))),
    rules: result.rules.map(r => ({entry: r.entry, ok: r.ok, checked: r.checked, refusals: r.refusals}))}
}

export function replay(c: Case, policy: Policy, file: string, run: string[], directory: string): Replay {
  try {
    const result = python<Omit<Replay, 'broken'>>({action: 'replay', file, entry: c.entry, run}, directory)
    const steps = result.steps.filter(s => !policy.method || s.call.method === policy.method)
    const broken = (!policy.method && !holds(policy.expr, result.initial!, result.initial!)) || steps.some(s => !holds(policy.expr, s.before, s.after))
    return {...result, broken}
  } catch (e) { return {ok: false, broken: false, steps: [], why: e instanceof Error ? e.message : String(e)} }
}

export async function measure(c: Case): Promise<Row> {
  const root = mkdtempSync(join(tmpdir(), 'upstream-mutants-'))
  try {
    const prepared = prepare(c, root), parent = materialize(c, root, 'baseline', prepared.source)
    const baseline = await inspect(parent.file), mutants: Row['mutants'] = []
    for (const mutation of prepared.mutations) {
      const target = materialize(c, root, mutation.id, mutation.source), side = await inspect(target.file)
      const replays: Row['mutants'][number]['replays'] = []
      for (const policy of c.policies) {
        const law = side.claims.find(l => l.name === policy.name && l.expr === policy.expr && l.verdict === 'broken' && l.run?.length)
        if (law?.run) replays.push({policy, mutant: replay(c, policy, target.file, law.run, target.directory), parent: replay(c, policy, parent.file, law.run, parent.directory)})
      }
      const detected = baseline.fullyRead && side.fullyRead && baseline.claims.length > 0 && baseline.claims.every(l => l.verdict === 'proven') && replays.some(r => r.mutant.ok && r.mutant.broken && r.mutant.steps.length > 0 && r.parent.ok && !r.parent.broken && r.parent.steps.length > 0)
      const {source: _source, ...edit} = mutation
      mutants.push({...edit, side, detected, replays})
    }
    return {id: c.id, budgetMs, harness: harness(), provenance: c, baseline, mutants}
  } finally { rmSync(root, {recursive: true, force: true}) }
}

if (import.meta.main) {
  const ids = process.argv.slice(2)
  for (const c of cases.filter(c => !ids.length || ids.includes(c.id))) console.log('UPSTREAM_RESULT ' + JSON.stringify(await measure(c)))
}
