// The real-world corpus's score (README.md).
//   bun research/realworld/score.ts --one <item id> <law index> [--ms 60000]   one law, its verdict as JSON (a job)
//   bun research/realworld/score.ts --item <item id> [--ms 5000]               an item's laws in this process (quick)
//   bun research/realworld/score.ts --from <dir> [--md out.md] [--json out]    the tables and the score from jobs.ts's run
// Each law is proven with nothing stated beyond the rule and the law (lib.ts): an outcome is `proven` (proven and
// checked by the kernel), `refuted` (a run from the start that breaks it, the run in the log), `unknown` (neither,
// within the search's budget) or `timeout` (the job was killed). triage/*.json says, for each refuted law, whether the
// original code really does what the run shows (`bug`), or the rule (`model`) or the law (`law`) was wrong and how.
import {readFileSync, readdirSync, writeFileSync, existsSync} from 'node:fs'
import {corpus} from './corpus.ts'
import {GAPS, type RealItem} from './lib.ts'
import type {Verdict} from '../../core/dsl.ts'

const arg = (k: string) => { const i = process.argv.indexOf(k); return i < 0 ? undefined : process.argv[i + 1] }
const ms = Number(arg('--ms') ?? 60_000)

type Outcome = 'proven' | 'refuted' | 'unknown' | 'timeout' | 'error'
type Run = {item: string, law: number, name: string, outcome: Outcome, ms: number, goal?: string, stuck?: string, why?: string, run?: Verdict['run'], witness?: Record<string, number>, found?: string[], error?: string}
const outcome = (v: Verdict): Outcome => (v.proven && v.checked ? 'proven' : v.run ? 'refuted' : 'unknown')
function foundText(v: Verdict): string[] | undefined {
  const f = v.found
  if (!f) return undefined
  return [...(f.rank ? [`rank ${f.rank}`] : []), ...(f.laws ?? []).map(l => l.text), ...Object.entries(f.lemmas ?? {}).flatMap(([n, l]) => [...(l.lemmas ?? []), ...(l.between ?? [])].map(t => `${n}: ${t}`)), ...(f.facts ?? [])]
}
const runLaw = (it: RealItem, k: number): Run => {
  const l = it.laws[k]
  if (!l) throw new Error(`${it.id} has no law ${k}`)
  const t = performance.now()
  try {
    const v = l.prove(ms), found = foundText(v)
    return {item: it.id, law: k, name: l.name, outcome: outcome(v), ms: Math.round(performance.now() - t), goal: v.goal, stuck: v.stuck, ...(v.why ? {why: v.why.slice(0, 400)} : {}),
      ...(v.run ? {run: v.run} : {}), ...(v.witness && !v.run ? {witness: v.witness} : {}), ...(found?.length ? {found} : {})}
  } catch (e) {
    return {item: it.id, law: k, name: l.name, outcome: 'error', ms: Math.round(performance.now() - t), error: String((e as Error).stack ?? e).slice(0, 600)}
  }
}
const byId = (id: string) => { const it = corpus.find(i => i.id === id); if (!it) { console.error(`no item ${id}`); process.exit(2) } return it }

const one = arg('--one')
if (one) {
  console.log(JSON.stringify(runLaw(byId(one), Number(process.argv[process.argv.indexOf('--one') + 2]))))
  process.exit(0)
}
const item = arg('--item')
if (item) {
  const it = byId(item)
  for (let k = 0; k < it.laws.length; k++) {
    const r = runLaw(it, k)
    console.log(`${r.outcome.padEnd(8)} ${String(r.ms).padStart(6)} ms  ${r.name}${r.found ? `  [found: ${r.found.join('; ')}]` : ''}${r.outcome !== 'proven' ? `  (${[r.goal, r.stuck, r.why, r.error].filter(Boolean).join('; ').slice(0, 300)})` : ''}`)
    if (r.run) console.log(`         run: ${JSON.stringify(r.run)}`)
  }
  process.exit(0)
}

// --from: the logs of jobs.ts's jobs, each the job's key (`<item id>#<law index>`) and then its verdict as the last line.
const from = arg('--from')
if (!from) { console.error('--one <id> <k> | --item <id> | --from <dir>'); process.exit(2) }
const runs = new Map<string, Run>()
for (const f of readdirSync(from).filter(f => f.endsWith('.log'))) {
  const lines = readFileSync(`${from}/${f}`, 'utf8').trim().split('\n'), key = lines[0]!, hash = key.lastIndexOf('#')
  const [id, k] = [key.slice(0, hash), Number(key.slice(hash + 1))]
  let r: Run
  try { r = JSON.parse(lines.at(-1)!) as Run } catch { r = {item: id, law: k, name: corpus.find(i => i.id === id)?.laws[k]?.name ?? '?', outcome: 'timeout', ms: 150_000} }
  runs.set(key, r)
}
type Triage = {verdict: 'bug' | 'model' | 'law', note: string, repro?: string}
// triage/*.json: `{"<item id>#<law name>": {verdict, note, repro}}`, merged.
const tdir = new URL('./triage/', import.meta.url)
const triage: Record<string, Triage> = Object.assign({}, ...(existsSync(tdir) ? readdirSync(tdir).filter(f => f.endsWith('.json')).sort().map(f => JSON.parse(readFileSync(new URL(f, tdir), 'utf8'))) : []))

const out: string[] = []
const p = (s = '') => out.push(s)
const pct = (a: number, b: number) => (b ? `${Math.round(1000 * a / b) / 10}%` : '-')
const median = (xs: number[]) => { const s = [...xs].sort((a, b) => a - b); return s.length ? (s.length % 2 ? s[(s.length - 1) / 2]! : (s[s.length / 2 - 1]! + s[s.length / 2]!) / 2) : NaN }
const lawRuns = corpus.flatMap(it => it.laws.map((l, k) => ({it, l, k, r: runs.get(`${it.id}#${k}`)})))
const scored = lawRuns.filter(x => x.r)

// The score per domain.
const domains = [...new Set(corpus.map(i => i.domain))]
p('| Domain | Items | Fully expressible | Laws | Proven | Refuted | Unknown | Timeout |')
p('| --- | --- | --- | --- | --- | --- | --- | --- |')
const row = (name: string, items: RealItem[]) => {
  const ls = scored.filter(x => items.includes(x.it)), n = (o: Outcome) => ls.filter(x => x.r!.outcome === o).length
  p(`| ${name} | ${items.length} | ${items.filter(i => i.expressible === 'full').length} | ${ls.length} | ${n('proven')} | ${n('refuted')} | ${n('unknown') + n('error')} | ${n('timeout')} |`)
}
for (const d of domains) row(d, corpus.filter(i => i.domain === d))
row('**all**', corpus)
p()
const proven = scored.filter(x => x.r!.outcome === 'proven')
p(`- Items: ${corpus.length}; fully expressible: ${corpus.filter(i => i.expressible === 'full').length} (${pct(corpus.filter(i => i.expressible === 'full').length, corpus.length)}); none of it: ${corpus.filter(i => i.expressible === 'none').length}.`)
const unstated = corpus.flatMap(i => i.unstated ?? [])
p(`- Laws: ${lawRuns.length} stated (${scored.length} run), ${unstated.length} more a reviewer would ask that the language can't state; proven with nothing stated: ${proven.length} (${pct(proven.length, scored.length)} of those run, ${pct(proven.length, scored.length + unstated.length)} counting the unstated).`)
for (const kind of ['safety', 'liveness', 'access', 'step'] as const) {
  const ks = scored.filter(x => x.l.kind === kind)
  p(`  - ${kind}: ${ks.filter(x => x.r!.outcome === 'proven').length} / ${ks.length}`)
}
p(`- Median time per law: ${median(scored.map(x => x.r!.ms))} ms over all laws run, ${median(proven.map(x => x.r!.ms))} ms over those proven.`)
const refuted = scored.filter(x => x.r!.outcome === 'refuted')
const tri = (v: Triage['verdict']) => refuted.filter(x => triage[`${x.it.id}#${x.l.name}`]?.verdict === v).length
p(`- Refuted: ${refuted.length}: real bugs ${tri('bug')}, modelling errors ${tri('model')}, law errors ${tri('law')}, not triaged ${refuted.length - tri('bug') - tri('model') - tri('law')}.`)
const viaSearch = proven.filter(x => x.r!.found?.length)
p(`- Proven only through the search's finds (invariants, lemmas, a rank): ${viaSearch.length} of ${proven.length}.`)
p()

// The gaps, ranked by the items they block (an item counts once per gap).
p('| Gap | Items | Of which wholly blocked | What |')
p('| --- | --- | --- | --- |')
const gapKeys = Object.keys(GAPS) as (keyof typeof GAPS)[]
const gapRows = gapKeys.map(g => ({g, items: corpus.filter(i => i.gaps.some(x => x.gap === g)), whole: corpus.filter(i => i.gaps.some(x => x.gap === g && x.blocks === 'item'))})).filter(x => x.items.length).sort((a, b) => b.items.length - a.items.length)
for (const {g, items, whole} of gapRows) p(`| ${g} | ${items.length} | ${whole.length} | ${GAPS[g]} |`)
p()

// Every law.
p('| Item | Law | Kind | Intent | Outcome | ms | What the search found, or where it stopped |')
p('| --- | --- | --- | --- | --- | --- | --- |')
const esc = (s: string) => s.replace(/\|/g, '\\|').replace(/\n/g, ' ')
for (const {it, l, r} of lawRuns) {
  const t = triage[`${it.id}#${l.name}`]
  const note = !r ? '' : r.outcome === 'proven' ? (r.found?.join('; ') ?? '') : r.outcome === 'refuted' ? `${t ? `**${t.verdict}**: ${t.note} ` : ''}run: ${JSON.stringify(r.run)}` : [r.goal, r.stuck, r.why, r.error].filter(Boolean).join('; ')
  p(`| ${esc(it.id)} | ${esc(l.name)} | ${l.kind} | ${l.intent} | ${r?.outcome ?? 'not run'} | ${r?.ms ?? ''} | ${esc(note).slice(0, 400)} |`)
}
const missing = lawRuns.filter(x => !x.r)
if (missing.length) p(`\nnot in the run: ${missing.map(x => `${x.it.id}#${x.k}`).join(', ')}`)
console.log(out.join('\n'))
const md = arg('--md')
if (md) writeFileSync(md, out.join('\n') + '\n')
const json = arg('--json')
if (json) writeFileSync(json, JSON.stringify([...runs.values()], null, 1))
