// Mesa's continuous double auction (mesa/mesa-examples, examples/zi_double_auction/model/order_book.py, Apache-2.0):
// its OrderBook read as it ships, its priority laws stated as comment laws on try_match and decided by `check` (the
// rule checked against the code by running both), and every broken law's run replayed in the real code.
//
//   bun research/trading/mesa.ts --src <dir holding order_book.py at the pin> [--ms 30000] [--json out.json]
//
// Nothing is written but the laws: the copy checked is the pinned file with the comment lines below put above
// try_match. The methods read are stated (--methods): clear_all_crosses is a loop over try_match (loops over the state
// are outside the subset) and cancel_agent_order rebuilds a list by a comprehension (outside it too); see DESIGN.md.
import {execFileSync} from 'node:child_process'
import {mkdtempSync, readFileSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join, resolve} from 'node:path'
import {createHash} from 'node:crypto'
import {check} from '../../core/cli.ts'
import {extractPython} from '../../core/extract-py.ts'
import {buildLaw} from '../../core/laws.ts'
import {proveSteps} from '../../core/dsl.ts'

export const PIN = {repo: 'mesa/mesa-examples', commit: '5ab1c41db11bb36aa038824341e39110b15d1197', path: 'examples/zi_double_auction/model/order_book.py', licence: 'Apache-2.0',
  sha256: '54d2f7827495e49cf6fee437ceb32cb2aed6622a40a4bac2de5972816e1ec979'}
export const METHODS = ['submit_bid', 'submit_ask', 'best_bid', 'best_ask', 'spread', 'try_match']

// The laws, each with what its break looks like in the real code (a Python condition over the book before and after
// the last call: b0, a0 the lists before, b1, a1 after; the run is the one `check` found, replayed as it printed it).
const fill = (side: 'bids' | 'asks', o: string, j: string) => `${o} in self.${side}`
export const LAWS: {name: string, expr: string, broken: string}[] = [
  {name: 'the best bid fills', expr: `forall o in old(self.bids): forall j in old(self.bids): ${fill('bids', 'o', 'j')} or o.price > j.price or (o.price == j.price and o.timestamp <= j.timestamp)`,
    broken: 'any(o not in b1 and any(j.price > o.price or (j.price == o.price and j.timestamp < o.timestamp) for j in b0) for o in b0)'},
  {name: 'the best ask fills', expr: `forall o in old(self.asks): forall j in old(self.asks): ${fill('asks', 'o', 'j')} or o.price < j.price or (o.price == j.price and o.timestamp <= j.timestamp)`,
    broken: 'any(o not in a1 and any(j.price < o.price or (j.price == o.price and j.timestamp < o.timestamp) for j in a0) for o in a0)'},
  {name: 'a fill crosses', expr: 'forall b in old(self.bids): forall a in old(self.asks): b in self.bids or a in self.asks or a.price <= b.price',
    broken: 'any(b not in b1 and a not in a1 and a.price > b.price for b in b0 for a in a0)'},
  // (a list's items by their places: o <= j is "o was put in no later than j")
  {name: 'the earliest to arrive at the best price fills', expr: 'forall o in old(self.asks): forall j in old(self.asks): o in self.asks or o.price < j.price or (o.price == j.price and o <= j)',
    broken: 'any(o not in a1 and any(j.price == o.price and a0.index(j) < a0.index(o) for j in a0) for o in a0)'},
  {name: 'no agent trades with itself', expr: 'forall b in old(self.bids): forall a in old(self.asks): b in self.bids or a in self.asks or b.agent_id != a.agent_id',
    broken: 'any(b not in b1 and a not in a1 and b.agent_id == a.agent_id for b in b0 for a in a0)'},
]

if (import.meta.main) {
  const argv = process.argv.slice(2), opt = (k: string, d = '') => { const i = argv.indexOf(`--${k}`); return i < 0 ? d : argv[i + 1] ?? d }
  const src = resolve(opt('src')), ms = Number(opt('ms', '30000')), text = readFileSync(join(src, 'order_book.py'), 'utf8')
  const sha = createHash('sha256').update(text).digest('hex')
  if (sha !== PIN.sha256) throw new Error(`order_book.py is not the pinned file (sha256 ${sha})`)
  // The pinned file with the laws above try_match, nothing else changed.
  const at = text.indexOf('    def try_match(')
  const dir = mkdtempSync(join(tmpdir(), 'gdp-mesa-')), file = join(dir, 'order_book.py')
  writeFileSync(file, text.slice(0, at) + LAWS.map(l => `    # gdp: law ${l.name}: ${l.expr}\n`).join('') + text.slice(at))
  const t0 = performance.now(), {rules} = await check([file], {ms, propose: false, methods: METHODS})
  const r = rules[0]!
  console.log(`${PIN.repo}@${PIN.commit.slice(0, 7)} ${PIN.path} (${PIN.licence}): ${r.ok ? 'read' : 'refused'} in ${Math.round(performance.now() - t0)} ms`)
  if (!r.ok) {
    // (the reading's own refusals: the class named)
    const x = extractPython(file, {entry: 'OrderBook', methods: METHODS})
    console.log(JSON.stringify([...r.refusals, ...x.refusals], null, 1), x.evidence?.mismatch ?? '')
    process.exit(2)
  }
  for (const n of r.notes) console.log(`  note: ${n}`)
  const out: unknown[] = []
  for (const l of r.laws) {
    const law = LAWS.find(x => x.name === l.name)!
    console.log(`\n${l.verdict.padEnd(8)} ${l.name} (${l.ms} ms)${l.why ? ` -- ${l.why}` : ''}`)
    let replay: string | undefined
    if (l.run) {
      for (const s of l.run) console.log(`    ${s}`)
      // The run in the real code: each call as printed, the law's break checked on the lists before and after the last.
      // (an argument the rule reads nowhere is left out of the run: the check gives it 0, so does the replay)
      const calls = l.run.filter(s => !s.startsWith('made with')).map(s => `call(${JSON.stringify(/^(\w+)/.exec(s)![1])}, ${s.replace(/ with .*$/, '').replace(/^\w+\(/, '').replace(/\)$/, '') || ''})`.replace(/, \)$/, ')'))
      const py = ['import inspect, sys', `sys.path.insert(0, ${JSON.stringify(src)})`, 'from order_book import OrderBook', 'b = OrderBook()',
        'def call(name, **kw):', '  f = getattr(b, name)', '  return f(**{p: kw.get(p, 0) for p in inspect.signature(f).parameters})',
        ...calls.slice(0, -1), 'b0, a0 = list(b.bids), list(b.asks)', calls.at(-1)!, 'b1, a1 = list(b.bids), list(b.asks)', `print('broken' if ${law.broken} else 'holds')`].join('\n')
      replay = execFileSync('python3', ['-c', py], {encoding: 'utf8'}).trim()
      console.log(`    replayed in the real code: ${replay}`)
    }
    out.push({...l, ...(replay ? {replay} : {})})
  }
  // Each proven law again with no invariant beside it: a law of try_match's step from every state of the lists, so
  // from every state the methods left out reach too (clear_all_crosses steps try_match; cancel_agent_order removes).
  const x = extractPython(file, {methods: METHODS})
  for (const l of r.laws.filter(y => y.verdict === 'proven')) {
    const b = buildLaw(x, {name: l.name, expr: l.expr, method: 'try_match'})
    const v = proveSteps(x.rule as never, [], [b.law], {search: false})
    console.log(`from every state, no invariant: ${v.proven && v.checked ? 'proven' : 'not proven'}  ${l.name}`)
    ;(out.find(o => (o as {name: string}).name === l.name) as Record<string, unknown>).everyState = v.proven && v.checked
  }
  const json = opt('json')
  if (json) writeFileSync(json, JSON.stringify({pin: PIN, notes: r.notes, laws: out}, null, 1))
}
