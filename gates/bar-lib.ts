// The bar's benchmarks: how each is launched in a tree, how its run directory reads as one observation per task, and
// the comparison of two sides' observations (gates/bar.ts runs them, gates/bar-calibrate.ts reads past runs with them).
// A group is one launch (ITS gives two views: the task's statement, `gdp`, and per component, `gdp-scc`); a view is
// one table of the report. Every reader mirrors the summary script of its runner (compare/*/summary.ts,
// research/*/score.ts --from), so a figure here is the figure those print.
import {existsSync, readFileSync, readdirSync} from 'node:fs'

export type Obs = {answer: string, solved: boolean, wrong?: boolean, disputed?: boolean, secs: number}
export type Rows = Map<string, Obs>
export type View = {key: string, title: string, limit: number, family: (task: string) => string, parse: (dir: string, tree: string) => Rows, headline: (rows: Rows) => Record<string, number>}

const lines = (f: string) => existsSync(f) ? readFileSync(f, 'utf8').split('\n').filter(Boolean) : []
const jsonl = <T>(f: string): T[] => lines(f).flatMap(l => { try { return [JSON.parse(l) as T] } catch { return [] } })
const count = (rows: Rows, f: (o: Obs) => boolean) => [...rows.values()].filter(f).length
const dirOf = (t: string, k: number) => t.split('/').slice(0, k).join('/')

// ---------------------------------------------------------------------------------------------- the compare runners
type Row = {tool: string, task: string, answer: string, seconds: number, expected?: string}

function chcRows(dir: string, tree: string): Rows {
  const votes = new Map<string, string | null>()
  if (existsSync(`${dir}/tasks.json`)) for (const t of JSON.parse(readFileSync(`${dir}/tasks.json`, 'utf8')) as {task: string, vote: string | null}[]) votes.set(t.task, t.vote)
  const dfile = `${tree}/compare/chc/disputed.json`
  const disputes = existsSync(dfile) ? JSON.parse(readFileSync(dfile, 'utf8')) as Record<string, {answer: string}> : {}
  const out: Rows = new Map()
  for (const r of jsonl<Row>(`${dir}/results.jsonl`)) {
    if (r.tool !== 'gdp') continue
    const answered = r.answer === 'sat' || r.answer === 'unsat', disputed = answered && disputes[r.task]?.answer === r.answer
    const decided = votes.get(r.task) != null, wrong = answered && !disputed && decided && r.answer !== r.expected
    out.set(r.task, {answer: r.answer, solved: answered && !disputed && !wrong, wrong, disputed, secs: r.seconds})
  }
  return out
}

const decidedTerm = (a: string) => a === 'terminates' || a === 'nonterminating'
const termRows = (tool: string) => (dir: string): Rows => {
  const out: Rows = new Map()
  for (const r of jsonl<Row>(`${dir}/results.jsonl`)) {
    if (r.tool !== tool) continue
    const d = decidedTerm(r.answer), wrong = d && !!r.expected && r.answer !== r.expected
    out.set(r.task, {answer: r.answer, solved: d && !wrong, wrong, secs: r.seconds})
  }
  return out
}
const termHead = (rows: Rows) => ({solved: count(rows, o => o.solved), terminates: count(rows, o => o.solved && o.answer === 'terminates'), nonterminating: count(rows, o => o.solved && o.answer === 'nonterminating'),
  wrong: count(rows, o => !!o.wrong), unknown: count(rows, o => o.answer === 'unknown'), timeout: count(rows, o => o.answer === 'timeout'), error: count(rows, o => o.answer === 'error'), tasks: rows.size})

// TIP's theorems: a gdp-wired refutation is the statement false as TIP writes it (solve.ts answers refuted only where
// TIP's evaluator confirms it), not wrong; a rival's refutation of a theorem is (compare/tip/summary.ts).
const tipRows = (tool: string) => (dir: string): Rows => {
  const out: Rows = new Map()
  for (const r of jsonl<Row>(`${dir}/results.jsonl`)) if (r.tool === tool) out.set(r.task, {answer: r.answer, solved: r.answer === 'proven', wrong: tool !== 'gdp' && r.answer === 'refuted', secs: r.seconds})
  return out
}
const tipHead = (rows: Rows) => ({proven: count(rows, o => o.solved), refuted: count(rows, o => o.answer === 'refuted'), wrong: count(rows, o => !!o.wrong), unknown: count(rows, o => o.answer === 'unknown'),
  timeout: count(rows, o => o.answer === 'timeout'), unsupported: count(rows, o => o.answer === 'unsupported'), error: count(rows, o => o.answer === 'error'), tasks: rows.size})

// ------------------------------------------------------------------------------------------- modal/run.py job lists
// A job's log: research/*/jobs.ts echo the key first, the verdict JSON is the last line (score.ts --from's reading).
export function jobLogs(dir: string): {job: string, key: string, last: string, text: string}[] {
  if (!existsSync(dir)) return []
  return readdirSync(dir).filter(f => f.endsWith('.log')).map(f => {
    const text = readFileSync(`${dir}/${f}`, 'utf8'), ls = text.split('\n--- stderr ---')[0]!.trim().split('\n')
    return {job: f.slice(0, -4), key: ls[0] ?? '', last: ls.at(-1) ?? '', text}
  })
}
export const keyOfCmd = (cmd: string) => /echo '((?:[^']|'\\'')*)';/.exec(cmd)?.[1]?.replace(/'\\''/g, "'")

type FRun = {proven?: boolean, checked?: boolean, ms?: number, timeout?: boolean, error?: string}
const frontierRows = (dir: string): Rows => {
  const broken = new Set<string>(existsSync(`${dir}/broken.json`) ? JSON.parse(readFileSync(`${dir}/broken.json`, 'utf8')) as string[] : [])
  const items = new Map<string, FRun[]>()
  for (const l of jobLogs(dir)) {
    let r: FRun
    try { r = JSON.parse(l.last) as FRun } catch { r = {proven: false, checked: false, ms: 0, timeout: true} }
    items.set(l.key, [...items.get(l.key) ?? [], r])
  }
  const out: Rows = new Map()
  for (const [id, rs] of items) {
    const won = rs.some(r => r.proven && r.checked), timeout = rs.some(r => r.timeout), error = rs.some(r => r.error)
    const secs = Math.max(...rs.map(r => (r.ms ?? 0) / 1000)), b = broken.has(id)
    const answer = won ? 'proven' : timeout ? 'timeout' : error ? 'error' : b ? 'refused' : 'not proven'
    out.set(id, {answer: b ? `broken: ${answer}` : answer, solved: b ? !won : won, wrong: b && won, secs})
  }
  return out
}
const frontierHead = (rows: Rows) => {
  const laws = [...rows.values()].filter(o => !o.answer.startsWith('broken')), broken = [...rows.values()].filter(o => o.answer.startsWith('broken'))
  return {proven: laws.filter(o => o.solved).length, laws: laws.length, refused: broken.filter(o => o.solved).length, broken: broken.length, wrong: broken.filter(o => o.wrong).length, timeout: count(rows, o => o.answer.endsWith('timeout'))}
}

const realworldRows = (dir: string): Rows => {
  const out: Rows = new Map()
  for (const l of jobLogs(dir)) {
    let r: {outcome: string, ms: number}
    try { r = JSON.parse(l.last) as {outcome: string, ms: number} } catch { r = {outcome: 'timeout', ms: 150_000} }
    out.set(l.key, {answer: r.outcome, solved: r.outcome === 'proven', secs: r.ms / 1000})
  }
  return out
}
const rwHead = (rows: Rows) => ({proven: count(rows, o => o.solved), refuted: count(rows, o => o.answer === 'refuted'), unknown: count(rows, o => o.answer === 'unknown' || o.answer === 'error'), timeout: count(rows, o => o.answer === 'timeout'), laws: rows.size})

// research/query's 332 step goals: the outcome, and the search as its counts (the same search when they all match).
export type Goal = {outcome: string, leaves?: number, splits?: number, searchMs: number, cdcl?: {decisions?: number, conflicts?: number, nodes?: number}}
export const goalSig = (g: Goal) => JSON.stringify([g.outcome, g.leaves, g.splits, g.cdcl?.decisions, g.cdcl?.conflicts, g.cdcl?.nodes])
export function goals(dir: string): Map<string, Goal> {
  const out = new Map<string, Goal>()
  for (const l of jobLogs(dir)) {
    const g = l.text.split('\n').find(x => x.startsWith('{"goal"'))
    if (g) try { out.set(l.job, JSON.parse(g) as Goal) } catch { /* a cut line: no row */ }
  }
  return out
}
const g332Rows = (dir: string): Rows => {
  const out: Rows = new Map()
  for (const l of jobLogs(dir)) if (l.job.startsWith('g332__')) out.set(l.job, {answer: 'missing', solved: false, secs: 0})
  for (const [k, g] of goals(dir)) out.set(k, {answer: g.outcome, solved: g.outcome === 'proven', secs: g.searchMs / 1000})
  return out
}

// modal/run.py's summary.tsv: a job passes on exit 0.
export function summaryRows(dir: string): Rows {
  const out: Rows = new Map()
  for (const l of lines(`${dir}/summary.tsv`)) {
    const [name, code, secs] = l.split('\t')
    out.set(name!, {answer: `exit ${code}`, solved: code === '0', secs: Number(secs)})
  }
  return out
}
const suiteHead = (rows: Rows) => ({passed: count(rows, o => o.solved), failed: count(rows, o => !o.solved), jobs: rows.size, job_s: Math.round([...rows.values()].reduce((s, o) => s + Math.max(0, o.secs), 0) * 10) / 10})
const leanHead = (rows: Rows) => ({checked: count(rows, o => o.solved), sampled: rows.size, max_s: Math.max(0, ...[...rows.values()].map(o => o.secs))})

// The 1-vCPU tests: bun test's `(pass) name [ms]` per test, per job.
export function testTimes(dir: string): {tests: Map<string, number[]>, failed: string[]} {
  const tests = new Map<string, number[]>(), failed: string[] = []
  for (const l of jobLogs(dir)) {
    const suite = l.job.split('-').at(-2) ?? l.job
    if (l.text.includes('(fail)') || /\b[1-9]\d* fail\b/.test(l.text)) failed.push(l.job)
    for (const m of l.text.matchAll(/\(pass\) (.*?) \[([\d.]+)(ms|s)\]/g)) {
      const k = `${suite} | ${m[1]}`
      tests.set(k, [...tests.get(k) ?? [], Number(m[2]) * (m[3] === 's' ? 1000 : 1)])
    }
  }
  return {tests, failed}
}

// ------------------------------------------------------------------------------------------------------- the views
const realFamily = (k: string) => k.split('/')[0] ?? k
// A CHC task's directory, and for Lustre's 766 the system's name (DRAGON, car, metros, ...)
const chcFamily = (t: string) => { const d = t.split('/').slice(0, -1).join('/'); return d.endsWith('/lustre') ? `${d}/${/^[A-Za-z]+/.exec(t.split('/').at(-1)!)?.[0] ?? ''}` : d }
export const VIEWS: Record<string, View> = {
  chc: {key: 'chc', title: 'CHC-COMP LIA-Lin', limit: 60, family: chcFamily, parse: chcRows,
    headline: rows => ({solved: count(rows, o => o.solved), sat: count(rows, o => o.solved && o.answer === 'sat'), unsat: count(rows, o => o.solved && o.answer === 'unsat'), wrong: count(rows, o => !!o.wrong),
      disputed: count(rows, o => !!o.disputed), unknown: count(rows, o => o.answer === 'unknown'), timeout: count(rows, o => o.answer === 'timeout'), error: count(rows, o => o.answer === 'error'), tasks: rows.size})},
  its: {key: 'its', title: 'TermComp ITS, the task\'s statement (gdp)', limit: 60, family: t => dirOf(t, 2), parse: termRows('gdp'), headline: termHead},
  'its-scc': {key: 'its-scc', title: 'TermComp ITS, per component (gdp-scc)', limit: 60, family: t => dirOf(t, 2), parse: termRows('gdp-scc'), headline: termHead},
  sv: {key: 'sv', title: 'SV-COMP termination (gdp)', limit: 60, family: t => dirOf(t, 1), parse: termRows('gdp'), headline: termHead},
  'sv-scc': {key: 'sv-scc', title: 'SV-COMP termination, per component (gdp-scc)', limit: 60, family: t => dirOf(t, 1), parse: termRows('gdp-scc'), headline: termHead},
  tip: {key: 'tip', title: 'TIP 2015 (gdp)', limit: 60, family: t => dirOf(t, 1), parse: tipRows('gdp'), headline: tipHead},
  'tip-cvc5': {key: 'tip-cvc5', title: 'TIP 2015, cvc5 --quant-ind', limit: 60, family: t => dirOf(t, 1), parse: tipRows('cvc5'), headline: tipHead},
  'tip-cvc5cg': {key: 'tip-cvc5cg', title: 'TIP 2015, cvc5 --conjecture-gen', limit: 60, family: t => dirOf(t, 1), parse: tipRows('cvc5cg'), headline: tipHead},
  'tip-vampire': {key: 'tip-vampire', title: 'TIP 2015, Vampire', limit: 60, family: t => dirOf(t, 1), parse: tipRows('vampire'), headline: tipHead},
  f1: {key: 'f1', title: 'Frontier corpus, round 1', limit: 60, family: t => t.split('/')[0] ?? t, parse: frontierRows, headline: frontierHead},
  f2: {key: 'f2', title: 'Frontier corpus, round 2', limit: 60, family: t => t.split('/').slice(0, 2).join('/'), parse: frontierRows, headline: frontierHead},
  rw: {key: 'rw', title: 'The real-world corpus', limit: 60, family: realFamily, parse: realworldRows, headline: rwHead},
  g332: {key: 'g332', title: 'research/dag\'s 332 step goals', limit: 55, family: t => t.split('__')[1] ?? t, parse: g332Rows,
    headline: rows => ({proven: count(rows, o => o.solved), goals: rows.size, search_s: Math.round([...rows.values()].reduce((s, o) => s + o.secs, 0) * 10) / 10})},
  suite: {key: 'suite', title: 'The suite, by default', limit: 900, family: t => t.replace(/-\d+$/, ''), parse: summaryRows, headline: suiteHead},
  'suite-usual': {key: 'suite-usual', title: 'The suite, --usual', limit: 900, family: t => t.replace(/-\d+$/, ''), parse: summaryRows, headline: suiteHead},
  lean: {key: 'lean', title: 'Lean: recurrent sets of the ITS run checked again', limit: 2100, family: () => 'lean', headline: leanHead,
    // (a job's stdout has Lean's `time`, its stderr the export's)
    parse: dir => new Map(jobLogs(dir).map(l => {
      const ok = /lean-exit 0\b/.test(l.text), m = /real\s+(\d+)m([\d.]+)s/.exec(l.text.split('--- stderr ---')[0]!)
      return [l.key || l.job, {answer: ok ? 'checked' : 'not checked', solved: ok, secs: m ? Number(m[1]) * 60 + Number(m[2]) : 0}]
    }))},
}

// ------------------------------------------------------------------------------------------------- the comparison
export type Samples = {cand: Obs[], base: Obs[]}
export type TaskCmp = {task: string, kind: 'gained' | 'lost' | 'noise' | 'wrong', solid: boolean, atLimit: boolean, inBand: boolean, cand: string, base: string, samples: Samples}

const solvedOf = (os: Obs[]) => os.filter(o => o.solved).length
const majority = (os: Obs[]) => os.length > 0 && solvedOf(os) * 2 > os.length
// A task's base runs disagree, or one of them solved it in the last quarter of the limit: the noise band, where a flip
// is expected between two runs of the same commit.
export const inBand = (base: Obs[], limit: number) => base.length > 0 && (new Set(base.map(o => o.solved)).size > 1 || base.some(o => o.solved && o.secs >= 0.75 * limit))
// The tasks whose first-pass observation differs from the base's: solved on one side only (the base's majority over
// its runs), or decided both ways (sat against unsat: one of them is wrong), or wrong.
export function differing(cand: Rows, base: Rows[]): string[] {
  const out: string[] = []
  for (const [t, c] of cand) {
    const bs = base.map(b => b.get(t)).filter((o): o is Obs => !!o)
    if (!bs.length) continue
    const decidedOther = bs.some(b => b.solved && c.solved && b.answer !== c.answer)
    if (c.wrong || decidedOther || c.solved !== majority(bs)) out.push(t)
  }
  return out
}
const fmtSamples = (os: Obs[]) => `${solvedOf(os)}/${os.length}`
export function compareTasks(tasks: string[], samples: Map<string, Samples>, limit: number): TaskCmp[] {
  return tasks.map(task => {
    const s = samples.get(task) ?? {cand: [], base: []}, rc = solvedOf(s.cand) / Math.max(1, s.cand.length), rb = solvedOf(s.base) / Math.max(1, s.base.length)
    const decided = (os: Obs[]) => new Set(os.filter(o => o.solved).map(o => o.answer))
    const both = new Set([...decided(s.cand), ...decided(s.base)])
    const wrong = s.cand.some(o => o.wrong) || both.size > 1
    const kind = wrong ? 'wrong' : majority(s.cand) && !majority(s.base) ? 'gained' : !majority(s.cand) && majority(s.base) ? 'lost' : 'noise'
    const solid = kind === 'gained' ? rc === 1 && rb === 0 : kind === 'lost' ? rc === 0 && rb === 1 : false
    const all = [...s.cand, ...s.base]
    // a flip at the time limit: some run answered it only in the last quarter of the limit
    const atLimit = all.some(o => o.solved && o.secs >= 0.75 * limit)
    return {task, kind, solid, atLimit, inBand: inBand(s.base.slice(0, 3), limit), cand: fmtSamples(s.cand), base: fmtSamples(s.base), samples: s}
  })
}

// ------------------------------------------------------------------------------------------------------ the dev set
// A deterministic order inside a stratum (FNV-1a of the name), so a dev set is the same on every machine.
export const hash = (s: string) => { let h = 2166136261; for (let i = 0; i < s.length; i++) h = Math.imul(h ^ s.charCodeAt(i), 16777619); return h >>> 0 }
export type Status = 'early' | 'late' | 'unsolved' | 'refused'
export const statusOf = (o: Obs, limit: number): Status => o.solved ? (o.secs >= limit / 3 ? 'late' : 'early') : o.answer === 'unsupported' || o.answer === 'refused' || o.answer.startsWith('broken') ? 'refused' : 'unsolved'
// A stratum is a family and how the reference run of main did on the task. Each gets a share of the size by its count
// times its status's weight (the late and the unsolved, where flips and gains are, count more), at least one task.
const WEIGHT: Record<Status, number> = {early: 1, late: 4, unsolved: 2, refused: 0.25}
export type Dev = {size: number, of: number, reference: string, strata: Record<string, {n: number, of: number}>, tasks: Record<string, string>}
export function devSet(view: View, ref: Rows, size: number, reference: string): Dev {
  const strata = new Map<string, string[]>()
  for (const [t, o] of ref) { const k = `${view.family(t)} | ${statusOf(o, view.limit)}`; strata.set(k, [...strata.get(k) ?? [], t]) }
  const total = [...strata].reduce((s, [k, ts]) => s + ts.length * WEIGHT[k.split(' | ')[1] as Status], 0)
  const out: Dev = {size: 0, of: ref.size, reference, strata: {}, tasks: {}}
  for (const [k, ts] of [...strata].sort((a, b) => a[0].localeCompare(b[0]))) {
    const n = Math.min(ts.length, Math.max(1, Math.round(size * ts.length * WEIGHT[k.split(' | ')[1] as Status] / total)))
    const pick = [...ts].sort((a, b) => hash(a) - hash(b) || a.localeCompare(b)).slice(0, n)
    out.strata[k] = {n, of: ts.length}
    for (const t of pick.sort()) out.tasks[t] = k
  }
  out.size = Object.keys(out.tasks).length
  return out
}
// The full-set delta the dev set predicts: each stratum's delta scaled by its count over its sample.
export function predict(dev: Dev, cand: Rows, base: Rows): {raw: number, scaled: number} {
  let raw = 0, scaled = 0
  for (const [t, k] of Object.entries(dev.tasks)) {
    const d = Number(!!cand.get(t)?.solved) - Number(!!base.get(t)?.solved), s = dev.strata[k]
    raw += d
    scaled += s ? d * s.of / s.n : d
  }
  return {raw, scaled: Math.round(scaled * 10) / 10}
}
export const solvedCount = (rows: Rows, tasks?: Set<string>) => [...rows].filter(([t, o]) => o.solved && (!tasks || tasks.has(t))).length
export function pearson(xs: number[], ys: number[]): number {
  const n = xs.length, mx = xs.reduce((a, b) => a + b, 0) / n, my = ys.reduce((a, b) => a + b, 0) / n
  let sxy = 0, sxx = 0, syy = 0
  for (let i = 0; i < n; i++) { sxy += (xs[i]! - mx) * (ys[i]! - my); sxx += (xs[i]! - mx) ** 2; syy += (ys[i]! - my) ** 2 }
  return sxx && syy ? sxy / Math.sqrt(sxx * syy) : NaN
}
