// The tasks another tool answered and gdp-wired didn't, by what is missing:
//   bun compare/term/failures.ts <diag-koat dir, or -> <run dirs: the tools' rows, later replacing earlier> [--bench <root>]
// (--bench: the tasks' directory, TPDB-ARI's checkout, for the split of "no turn sampled" below)
// Terminating (KoAT2 or LoAT said so; neither gdp-wired translation proved it): the technique KoAT2's proof used
// (`koat2 analyse --termination --show-proof`: the depth of each multiphase ranking function, MPRF), read beside where
// the SCC translation (gdp-scc) stopped:
//   - multiphase: an MPRF of depth 2 or more in KoAT2's proof (no tuple in order found by the runs did it)
//   - a rank fitted to the params: the runs gave a rank reading a param (a<j>, a start value the loop keeps or
//     starts from) and the kernel refused it: the LP's fit over values constant along each run
//   - a rank the kernel refused, no param read: the runs gave a rank, wrong off the runs (a nondeterministic choice the
//     runs draw small: a reset to any value) or needing an invariant inferLaws didn't find
//   - no turn sampled: the runs never took a turn of the component (its guard needs values past the runs' bounds, or
//     an equation between inputs)
//   - no rank fits the sampled turns: the runs' edges admit no linear rank in order, nor one of degree 2
//   - out of time, or the search threw
// The ones only the location-free translation missed (gdp-scc proved them, gdp didn't) are counted apart: one rank for
// the whole program, over the location's number, is what failed there.
// Nonterminating (LoAT said so; no lasso found): where gdp-wired's lasso runs got (LoAT's proofs, a recurrent set
// each, don't say whether a state repeats: the README splits a sample of them by hand).
import {readFileSync, statSync} from 'node:fs'
import {parseAri, type Sx} from './ari.ts'
import {planRule} from './translate.ts'
import {components} from './scc.ts'

type Row = {tool: string, task: string, answer: string, seconds: number, stages?: Record<string, unknown>[], out?: string}
const argv = process.argv.slice(2), bi = argv.indexOf('--bench'), bench = bi >= 0 ? argv.splice(bi, 2)[1] : undefined
const [koatDir, ...dirs] = argv
const read = (d: string): Row[] => readFileSync(`${d}/results.jsonl`, 'utf8').split('\n').filter(Boolean).map(l => JSON.parse(l) as Row)
const rows = new Map<string, Row>()
for (const d of dirs) for (const r of read(d)) rows.set(`${r.tool}\t${r.task}`, r)
const get = (tool: string, task: string) => rows.get(`${tool}\t${task}`)
const tasks = [...new Set([...rows.values()].map(r => r.task))]
const ans = (tool: string, task: string) => get(tool, task)?.answer
const koat = new Map(koatDir === '-' ? [] : read(koatDir!).map(r => [r.task, r]))
const count = (xs: string[]) => { const m = new Map<string, number>(); for (const x of xs) m.set(x, (m.get(x) ?? 0) + 1); return [...m].sort((a, b) => b[1] - a[1]) }
const examples = new Map<string, string[]>()
const label = (k: string, task: string) => { examples.set(k, [...(examples.get(k) ?? []), task]); return k }

const depth = (out: string) => Math.max(0, ...[...out.matchAll(/of depth (\d+)/g)].map(m => Number(m[1])))
function sccWhy(task: string): string {
  const r = get('gdp-scc', task)
  if (!r) return 'no gdp-scc row'
  if (r.answer === 'timeout') return 'out of time'
  const rk = r.stages?.filter(s => s.stage === 'rank') ?? []
  const last = rk.at(-1)
  if (!last) return r.answer === 'unknown' ? 'out of time, or the search threw' : `no rank stage (${r.answer})`
  if (last.error) return 'out of time, or the search threw'
  const why = typeof last.why === 'string' ? last.why : ''
  const m = /drops on every turn of (\d+) sampled/.exec(why)
  if (m) return Number(m[1]) === 0 ? 'no turn sampled' : 'no rank fits the sampled turns'
  if (why.includes('no invariant found')) return /\ba\d+(\$n)?\b/.test(String(last.rank)) ? 'a rank fitted to the params' : 'a rank the kernel refused, no param read'
  return why.slice(0, 60) || 'other'
}

const term: string[] = [], nonterm: string[] = [], onlyA: string[] = [], refused: string[] = []
for (const t of tasks) {
  const ours = (a?: string) => a === 'terminates' || a === 'nonterminating'
  if (ans('gdp-scc', t) === 'terminates' && ans('gdp', t) !== 'terminates') onlyA.push(t)
  if (ours(ans('gdp', t)) || ours(ans('gdp-scc', t))) continue
  if (ans('gdp', t) === 'unsupported') { refused.push(t); continue }
  if (['koat2', 'loat', 'loat-abmc', 'uautomizer'].some(o => ans(o, t) === 'terminates')) {
    const k = koat.get(t), d = k?.answer === 'terminates' ? depth(k.out ?? '') : 0
    const by = k?.answer === 'terminates' || koatDir === '-' ? '' : ' (KoAT2 gave no proof; another tool did)'
    term.push(label(d >= 2 ? `multiphase rank (KoAT2's MPRF of depth ${d})` : `${sccWhy(t)}${by}`, t))
  } else if (['loat', 'loat-abmc', 'uautomizer'].some(o => ans(o, t) === 'nonterminating')) {
    // where gdp-wired's runs got: a run that never takes a turn (no rule's guard met by the drawn inputs), runs that
    // stop within a few turns on average, or long runs that never came back to a state
    const ls = get('gdp', t)?.stages?.filter(x => x.stage === 'lassos').at(-1)
    const runs = Number(ls?.runs ?? 0), turns = Number(ls?.turns ?? 0)
    nonterm.push(label(!ls ? 'no lasso stage (out of time before it)' : turns === 0 ? 'the runs take no turn' : turns / Math.max(1, runs) < 5 ? 'the runs stop within 5 turns on average' : 'long runs, no state repeated', t))
  }
}
console.log(`terminating by another tool, not by gdp-wired: ${term.length}`)
for (const [k, n] of count(term)) console.log(`  ${n}  ${k}   e.g. ${examples.get(k)!.slice(0, 3).map(x => x.split('/').pop()).join(', ')}`)
console.log(`nonterminating by another tool, no lasso: ${nonterm.length}`)
for (const [k, n] of count(nonterm)) console.log(`  ${n}  ${k}   e.g. ${examples.get(k)!.slice(0, 3).map(x => x.split('/').pop()).join(', ')}`)
console.log(`not translated (refused, see the summary's reasons), answered by another tool: ${refused.filter(t => ['koat2', 'loat', 'loat-abmc', 'uautomizer'].some(o => ['terminates', 'nonterminating'].includes(ans(o, t) ?? ''))).length}`)
console.log(`proven by the SCC translation and not the location-free one (one rank over pc failed): ${onlyA.length}`)
const deep = new Map<number, number>()
for (const k of koat.values()) if (k.answer === 'terminates') deep.set(depth(k.out ?? ''), (deep.get(depth(k.out ?? '')) ?? 0) + 1)
console.log('KoAT2 MPRF depth over its proofs read:', [...deep].sort((a, b) => a[0] - b[0]))

// "No turn sampled", split by what each component's rules ask of a turn's inputs (with --bench): an input an equation
// of the guard pins (2·x = y, not a definition), a constant past 64 in a guard (the runs draw up to 64), both, or
// neither (several nondeterministic values bounded together: each drawn alone, the guard rarely holds of all of them).
if (bench) {
  const vs = (x: Sx, o = new Set<string>()): Set<string> => { if (typeof x === 'string') o.add(x); else x.forEach(y => vs(y, o)); return o }
  const big = (x: Sx): boolean => (typeof x === 'string' ? /^\d+$/.test(x) && Number(x) > 64 : x.some(big))
  const split: string[] = []
  for (const t of examples.get('no turn sampled') ?? []) {
    const path = `${bench}/${t}`
    if (statSync(path).size > 2e6) { split.push('a file over 2 MB (not read)'); continue }
    let pinned = false, large = false
    for (const c of components(parseAri(readFileSync(path, 'utf8')))) {
      const locs = [...c.task.funs.keys()], seen = new Map<string, number>()
      for (const r of c.task.rules) {
        const k = seen.get(r.from) ?? 0
        seen.set(r.from, k + 1)
        const p = planRule(r, locs, k)
        for (const g of p.guard) { if (Array.isArray(g) && g[0] === '=' && [...vs(g)].some(v => p.inputs.includes(v))) pinned = true; if (big(g)) large = true }
      }
    }
    split.push(pinned && large ? 'both' : pinned ? 'an input pinned by an equation' : large ? 'a constant past 64 in a guard' : 'neither: several nondeterministic values bounded together')
  }
  console.log('"no turn sampled", by what the guards ask:', count(split))
}
