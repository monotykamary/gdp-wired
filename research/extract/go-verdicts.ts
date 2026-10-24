// The real-world corpus's laws (research/realworld/items/*.ts) on the rules the Go front end (core/extract-go.ts) reads
// from the corpus's Go code, beside the same laws on the item's rule by hand: each law stated again in the extracted
// rule's terms (its fields the struct's, its events the methods), proven the corpus's way (lib.ts: the default search
// at the budget given) with the extraction's own invariants beside it (a field within its type, a nil *big.Int holding
// 0), and the two verdicts compared. A law that reads what the code read doesn't keep has no statement there: listed.
//
//   bun research/extract/go-verdicts.ts --jobs > research/extract/go-verdict-jobs.json     one job per law
//   bun research/extract/go-verdicts.ts --one <case> <k> [--ms 60000]                       one law, both sides
//   bun research/extract/go-verdicts.ts --from <dir>                                        the rows of a batch
import {readFileSync, readdirSync} from 'node:fs'
import {join} from 'node:path'
import {type StepLaw, type Verdict, proveRule, proveSteps} from '../../core/dsl.ts'
import type {Law} from '../../core/machine.ts'
import {type GoExtraction, extractGo} from '../../core/extract-go.ts'
import {corpus} from '../realworld/corpus.ts'
import type {RealLaw} from '../realworld/lib.ts'
import {checkout} from './go-fetch.ts'

const here = import.meta.dir, args = process.argv.slice(2)
const arg = (k: string) => { const i = args.indexOf(k); return i < 0 ? undefined : args[i + 1] }
const ms = Number(arg('--ms') ?? 60_000)
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Any = any
type Src = {item: string, repo: string, commit: string, path: string}
const sources = JSON.parse(readFileSync(join(here, '../realworld/sources.json'), 'utf8')) as Src[]
type Stated = RealLaw | {unstated: string}
type Case = {id: string, item: string, path: string, entry: string, methods: string[], onError?: 'discard', laws: (x: GoExtraction) => Stated[]}
const inv = (x: GoExtraction, law: Law): RealLaw => ({name: law.name, kind: 'safety', intent: 'tests', why: '', form: 'invariant', prove: t => proveRule(x.rule as Any, [...(x.invariants ?? []), law], {search: {ms: t}})})
const stepOf = (x: GoExtraction, sl: StepLaw): RealLaw => ({name: sl.name, kind: 'step', intent: 'docs', why: '', form: 'step', prove: t => proveSteps(x.rule as Any, x.invariants ?? [], [sl], {search: {ms: t}})})
void stepOf
const cases: Case[] = [
  // Balance's methods the subset reads (go-run.ts's part: UpdateBalances and CommitInflight* read float64 fields and
  // shopspring/decimal, refused), one call a step; a failed call's writes dropped, as transaction_execution.go does.
  {id: 'blnk', item: 'ledger/blnk/balances', path: 'model/model.go', entry: 'Balance', methods: ['addCredit', 'addDebit', 'computeBalance', 'RollbackInflightCredit', 'RollbackInflightDebit'], onError: 'discard', laws: x => {
    const r = x.rule as Any
    return [
      inv(x, r.law('every balance is its credits less its debits', ({Balance, CreditBalance, DebitBalance}: Any) => Balance.eq(CreditBalance.minus(DebitBalance)))),
      inv(x, r.law('every inflight balance is its inflight credits less its inflight debits', ({InflightBalance, InflightCreditBalance, InflightDebitBalance}: Any) => InflightBalance.eq(InflightCreditBalance.minus(InflightDebitBalance)))),
      inv(x, r.law('no inflight debit is ever negative', ({InflightDebitBalance}: Any) => InflightDebitBalance.atLeast(0))),
      {unstated: 'it reads tC and tD, the sums of every balance\'s credits and debits, ghosts the item adds (one Balance\'s methods keep no sum over balances)'},
      {unstated: 'it reads tIC and tID, the sums of every balance\'s inflight credits and debits, ghosts the item adds'},
      {unstated: 'it reads Unbounded and MaxLimit, what each balance sourced under (ghosts the item adds from the overdraft settings of UpdateBalances, refused)'},
    ]
  }},
  // The item's rule is the CircuitBreaker (refused: a generic type, time.Now(), loops); what is extracted is its also,
  // counter.go's Counts, whose fields the item's laws don't read.
  {id: 'gobreaker', item: 'circuit breaker/gobreaker/CircuitBreaker', path: 'v2/counter.go', entry: 'Counts', methods: ['onRequest', 'onSuccess', 'onFailure', 'onExclusion', 'validRequests', 'clear'], laws: () =>
    Array.from({length: 7}, () => ({unstated: 'it reads the breaker\'s state, generation or expiry (CircuitBreaker\'s, refused); the source extracted is the item\'s also, counter.go\'s Counts, which keeps none of them'}))},
]

const verdictOf = (v: Verdict): string => (v.proven && v.checked ? 'proven' : v.run ? 'refuted' : 'unknown')
const prove = (l: RealLaw) => {
  const t = performance.now()
  try { const v = l.prove(ms); return {verdict: verdictOf(v), ms: Math.round(performance.now() - t), ...(v.proven ? {} : {goal: v.goal, stuck: v.stuck, why: v.why?.slice(0, 300)}), ...(v.run ? {run: v.run} : {})} } catch (e) { return {verdict: 'error', ms: Math.round(performance.now() - t), error: String((e as Error).message).slice(0, 300)} }
}
const extracted = (k: Case): GoExtraction => {
  const s = sources.find(x => x.item === k.item && x.path === k.path)!
  const dir = checkout(s.repo, s.commit, s.path.split('/').slice(0, -1).join('/'))
  const x = extractGo(dir, {entry: k.entry, methods: k.methods, ...(k.onError ? {onError: k.onError} : {}), check: {runs: 200, depth: 12, states: 400}})
  if (!x.ok) throw new Error(`${k.path} not extracted: ${JSON.stringify(x.refusals)}`)
  return x
}

if (args.includes('--jobs')) {
  const q = (s: string) => `'${s.replace(/'/g, `'\\''`)}'`
  const jobs = cases.flatMap(k => corpus.find(i => i.id === k.item)!.laws.map((_, j) => ({
    name: `go-corpus-${k.id}-${j}`,
    cmd: `bun install --frozen-lockfile >/dev/null 2>&1; . research/extract/go-setup.sh >/dev/null 2>&1; timeout -s KILL 280 bun research/extract/go-verdicts.ts --one ${q(k.id)} ${j} --ms 60000 2>&1 | tail -1`,
    cpu: 2.0, timeout: 330,
  })))
  console.log(JSON.stringify(jobs, null, 1))
  process.exit(0)
}
const oneAt = args.indexOf('--one')
if (oneAt >= 0) {
  const k = cases.find(x => x.id === args[oneAt + 1])!, j = Number(args[oneAt + 2]), item = corpus.find(i => i.id === k.item)!, law = item.laws[j]!
  const stated = k.laws(extracted(k))[j]!
  const hand = prove(law)
  const row = 'unstated' in stated
    ? {case: k.id, item: k.item, law: j, name: law.name, hand, extracted: {verdict: 'unstated', why: stated.unstated}}
    : {case: k.id, item: k.item, law: j, name: law.name, hand, extracted: prove(stated), agree: undefined as boolean | undefined}
  if ('agree' in row) row.agree = row.hand.verdict === row.extracted.verdict
  console.log(JSON.stringify(row))
  process.exit(0)
}
const from = arg('--from')
if (from) {
  const rows = readdirSync(from).filter(f => f.startsWith('go-corpus-') && f.endsWith('.log')).map(f => { const l = readFileSync(join(from, f), 'utf8').trim().split('\n').at(-1)!; try { return JSON.parse(l) } catch { return {file: f, error: l.slice(0, 300)} } })
  for (const r of rows) console.log(JSON.stringify(r))
  const stated = rows.filter(r => r.agree !== undefined)
  console.log(`${rows.length} laws: ${stated.length} stated on the extracted rule (${stated.filter(r => r.agree).length} agree, ${stated.filter(r => !r.agree).length} disagree), ${rows.filter(r => r.extracted?.verdict === 'unstated').length} unstated`)
}
