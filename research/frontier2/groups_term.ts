// The termination groups the corpus's items stand for: the tasks another tool answered and gdp-wired didn't, by where
// gdp-wired's search stopped on the task's own statement (compare/term/translate.ts's loop over every location, the
// `gdp` tool: what the items state), as compare/term/failures.ts classes them (it read the stronger per-component `gdp-scc`).
//   bun research/frontier2/groups_term.ts [--runs <runs dir>] [--bench <TPDB-ARI checkout>]
// The runs (under --runs, `runs` by default):
//   - TermComp ITS: gdp-wired's `gdp` rows from backends/term-gdp (boat, the code at the 0.21.0 release's parent);
//     LoAT, LoAT abmc and KoAT2 from supercomputer/term/full1 and koat-fix1 (KoAT2's reruns); KoAT2's proofs from
//     supercomputer/term/diag-koat (the depth of its multiphase ranking functions); `gdp-scc` from supercomputer/term/gdp2, only to
//     count how many of a class the per-component statement proved there
//   - SV-COMP: gdp-wired's rows and LoAT abmc's and KoAT2's on its translation from supercomputer/term/sv3, Ultimate Automizer
//     from supercomputer/term/sv2 (sv3 replacing sv2 where both have a tool's row)
// Classes, the first that applies:
//   - multiphase rank: KoAT2's proof has a multiphase ranking function of depth 2 or more (ITS only)
//   - no turn sampled / no rank fits the sampled turns: findRank's runs took no turn of the loop, or no rank of its
//     shapes (linear or degree 2, in order) drops on every sampled turn
//   - a rank fitted to the params: the runs gave a rank reading a param (a<j>: a start value the loop keeps) and the
//     kernel refused it; a rank the kernel refused, no param read: the runs gave a rank, wrong off the runs or needing
//     an invariant inferLaws didn't find
//   - out of time: no rank stage before the limit
// Nonterminating tasks (another tool's NO, no lasso found) are counted by where gdp-wired's lasso runs got: the library
// has no claim that some run never ends, so these are the language gap, not items.
import {readFileSync, statSync} from 'node:fs'
import {parseAri, type Sx} from '../../compare/term/ari.ts'
import {planRule} from '../../compare/term/translate.ts'
import {components} from '../../compare/term/scc.ts'
import {termItems} from './term.ts'

type Row = {tool: string, task: string, answer: string, stages?: Record<string, unknown>[], out?: string, why?: string}
const argv = process.argv.slice(2), opt = (k: string) => { const i = argv.indexOf(k); return i < 0 ? undefined : argv[i + 1] }
const root = opt('--runs') ?? 'runs', bench = opt('--bench')
const read = (d: string): Row[] => readFileSync(`${root}/${d}/results.jsonl`, 'utf8').split('\n').filter(Boolean).map(l => JSON.parse(l) as Row)
const count = (xs: string[]) => { const m = new Map<string, number>(); for (const x of xs) m.set(x, (m.get(x) ?? 0) + 1); return [...m].sort((a, b) => b[1] - a[1]) }
const depth = (out: string) => Math.max(0, ...[...out.matchAll(/of depth (\d+)/g)].map(m => Number(m[1])))

function why(r: Row | undefined): string {
  if (!r) return 'no gdp row'
  const last = r.stages?.filter(s => s.stage === 'rank').at(-1)
  if (!last) return r.answer === 'timeout' ? 'out of time' : `no rank stage (${r.answer})`
  if (last.error) return 'the search threw'
  const w = typeof last.why === 'string' ? last.why : ''
  const m = /drops on every turn of (\d+) sampled/.exec(w)
  if (m) return Number(m[1]) === 0 ? 'no turn sampled' : 'no rank fits the sampled turns'
  if (w.includes('no invariant found')) return /\ba\d+(\$n)?\b/.test(String(last.rank)) ? 'a rank fitted to the params' : 'a rank the kernel refused, no param read'
  return w.slice(0, 60) || 'other'
}

function report(title: string, dirs: string[], koatDir?: string, benchDir?: string, items: string[] = []) {
  const rows = new Map<string, Row>()
  for (const d of dirs) for (const r of read(d)) rows.set(`${r.tool}\t${r.task}`, r)
  const get = (tool: string, task: string) => rows.get(`${tool}\t${task}`), ans = (tool: string, task: string) => get(tool, task)?.answer
  const koat = new Map(koatDir ? read(koatDir).map(r => [r.task, r]) : [])
  const tasks = [...new Set([...rows.values()].map(r => r.task))].sort()
  const term = new Map<string, string[]>(), nonterm = new Map<string, string[]>(), add = (m: Map<string, string[]>, k: string, t: string) => m.set(k, [...(m.get(k) ?? []), t])
  let refusedAnswered = 0, sccProved = 0
  for (const t of tasks) {
    const g = ans('gdp', t)
    if (g === 'terminates' || g === 'nonterminating') continue
    const other = (a: string) => ['koat2', 'loat', 'loat-abmc', 'uautomizer'].some(o => ans(o, t) === a)
    if (g === 'unsupported') { if (other('terminates') || ['loat', 'loat-abmc', 'uautomizer'].some(o => ans(o, t) === 'nonterminating')) refusedAnswered++; continue }
    if (other('terminates')) {
      const k = koat.get(t), d = k?.answer === 'terminates' ? depth(k.out ?? '') : 0
      if (ans('gdp-scc', t) === 'terminates') sccProved++
      add(term, d >= 2 ? 'multiphase rank (KoAT2\'s proof: depth 2 or more)' : why(get('gdp', t)), t)
    } else if (['loat', 'loat-abmc', 'uautomizer'].some(o => ans(o, t) === 'nonterminating')) {
      const ls = get('gdp', t)?.stages?.filter(x => x.stage === 'lassos').at(-1), runs = Number(ls?.runs ?? 0), turns = Number(ls?.turns ?? 0)
      add(nonterm, !ls ? 'no lasso stage (out of time before it)' : turns === 0 ? 'the runs take no turn' : turns / Math.max(1, runs) < 5 ? 'the runs stop within 5 turns on average' : 'long runs, no state repeated', t)
    }
  }
  const total = (m: Map<string, string[]>) => [...m.values()].reduce((a, b) => a + b.length, 0)
  const show = (m: Map<string, string[]>) => [...m].sort((a, b) => b[1].length - a[1].length).forEach(([k, ts]) => console.log(`  ${ts.length}  ${k}   e.g. ${ts.slice(0, 4).map(x => x.split('/').pop()).join(', ')}`))
  console.log(`## ${title} (${dirs.join(', ')}${koatDir ? `; KoAT2's proofs ${koatDir}` : ''})`)
  console.log(`terminating by another tool, not by gdp-wired's gdp: ${total(term)} (of those, proven by gdp-scc in its run: ${sccProved})`)
  show(term)
  console.log(`nonterminating by another tool, no lasso: ${total(nonterm)}`)
  show(nonterm)
  console.log(`refused by the translation, answered by another tool: ${refusedAnswered}`)
  // each corpus item's task: the class it is in here, and where gdp-scc stopped in its run
  for (const t of items) console.log(`  item ${t}: ${[...term].find(([, ts]) => ts.includes(t))?.[0] ?? `not in a class (gdp: ${ans('gdp', t)})`}; gdp-scc: ${ans('gdp-scc', t) ?? '-'}, ${why(get('gdp-scc', t))}`)
  if (benchDir) {
    const vs = (x: Sx, o = new Set<string>()): Set<string> => { if (typeof x === 'string') o.add(x); else x.forEach(y => vs(y, o)); return o }
    const big = (x: Sx): boolean => (typeof x === 'string' ? /^\d+$/.test(x) && Number(x) > 64 : x.some(big))
    const split: string[] = []
    for (const t of term.get('no turn sampled') ?? []) {
      const path = `${benchDir}/${t}`
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
    console.log('"no turn sampled", by what the guards ask:', JSON.stringify(count(split)))
  }
  console.log('')
}
const items = (b: string) => [...new Set(termItems.filter(i => i.source?.benchmark === b).map(i => i.source!.task))]
report('TermComp ITS', ['supercomputer/term/full1', 'supercomputer/term/koat-fix1', 'supercomputer/term/gdp2', 'backends/term-gdp'], 'supercomputer/term/diag-koat', bench, items('TermComp ITS'))
report('SV-COMP termination', ['supercomputer/term/sv2', 'supercomputer/term/sv3'], undefined, undefined, items('SV-COMP termination'))
const sv = read('supercomputer/term/sv3').filter(r => r.tool === 'gdp' && r.answer === 'unsupported')
console.log(`SV-COMP: refused by the translation (supercomputer/term/sv3): ${sv.length}`, JSON.stringify(count(sv.map(r => String(r.why)))))
