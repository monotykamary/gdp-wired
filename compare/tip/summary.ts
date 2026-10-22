// The run's tables: `bun compare/tip/summary.ts runs/modal/tip/<name> [<dir> ...]`, each later directory giving the rows of
// the tools the ones before it don't have (a gdp-wired run beside another run's cvc5 and Vampire). Per tool, over the TIP 2015 theorems
// (isaplanner, prod, tip2015, grammars: every one true) and apart over `false/` (every one false): proven, refuted,
// wrong (a refutation of a theorem, a proof of a false one), the rest. For gdp-wired, the translation's coverage (the
// reasons refused, the changes to the statement), and every tool again on the tasks gdp-wired translated.
import {readFileSync} from 'node:fs'

type Stage = Record<string, unknown> & {stage?: string}
type Row = {tool: string, task: string, answer: string, seconds: number, stages?: Stage[], err?: string}
const rows: Row[] = []
for (const dir of process.argv.slice(2).filter(a => !a.startsWith('--'))) {
  const had = new Set(rows.map(r => r.tool))
  rows.push(...readFileSync(`${dir}/results.jsonl`, 'utf8').split('\n').filter(Boolean).map(l => JSON.parse(l) as Row).filter(r => !had.has(r.tool)))
}
const tools = ['gdp', 'cvc5', 'cvc5cg', 'vampire', 'gdptr'].filter(t => rows.some(r => r.tool === t))
const names: Record<string, string> = {gdp: 'gdp-wired (proveData)', cvc5: 'cvc5 1.4.2 --quant-ind', cvc5cg: 'cvc5 1.4.2 --quant-ind --conjecture-gen', vampire: 'Vampire 5.1.0 (induction schedule)', gdptr: 'gdp-wired (translation only)'}
const isFalse = (t: string) => t.startsWith('false/')
const count = <T>(xs: T[], f: (x: T) => string) => { const m = new Map<string, number>(); for (const x of xs) m.set(f(x), (m.get(f(x)) ?? 0) + 1); return [...m].sort((a, b) => b[1] - a[1]) }
const median = (xs: number[]) => { const s = [...xs].sort((a, b) => a - b); return s.length ? s[Math.floor(s.length / 2)]! : NaN }
const lastStage = (r: Row, k: string) => r.stages?.findLast(s => s.stage === k)
const str = (x: unknown) => (typeof x === 'string' ? x : '')
const why = (r: Row) => str(lastStage(r, 'answer')?.why)
const changesOf = (r: Row) => (lastStage(r, 'import')?.changes as string[] | undefined) ?? []
const fmt = (n: number) => n.toLocaleString('en-US')

const table = (title: string, keep: (r: Row) => boolean, theorems: boolean) => {
  const n = new Set(rows.filter(keep).map(r => r.task)).size
  console.log(`\n### ${title} (${fmt(n)} tasks)\n`)
  console.log(`| tool | proven | refuted | wrong | solved of ${fmt(n)} | median s of those solved | unknown | timeout | unsupported | error |`)
  console.log(`| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |`)
  for (const tool of tools.filter(t => t !== 'gdptr')) {
    const rs = rows.filter(r => r.tool === tool && keep(r)), k = (a: string) => rs.filter(r => r.answer === a).length
    const right = rs.filter(r => r.answer === (theorems ? 'proven' : 'refuted')), wrong = rs.filter(r => r.answer === (theorems ? 'refuted' : 'proven'))
    console.log(`| ${names[tool]} | ${k('proven')} | ${k('refuted')} | ${wrong.length} | ${right.length} | ${right.length ? median(right.map(r => r.seconds)).toFixed(2) : '-'} | ${k('unknown')} | ${k('timeout')} | ${k('unsupported')} | ${k('error')} |`)
    for (const w of wrong) console.log(`  WRONG ${tool} ${w.task}: ${w.answer}`)
  }
}
const gdp = rows.filter(r => r.tool === 'gdp' || r.tool === 'gdptr')
// translated: imported, and the translation agreeing with TIP's evaluator (an error there is a translator bug)
const translated = new Set(gdp.filter(r => lastStage(r, 'import') && !/translation disagrees/.test(why(r))).map(r => r.task))
table('TIP 2015 theorems', r => !isFalse(r.task), true)
if (rows.some(r => isFalse(r.task))) table('TIP false/ (false properties)', r => isFalse(r.task), false)
if (translated.size) {
  table('The theorems gdp-wired translated', r => !isFalse(r.task) && translated.has(r.task), true)
  table('...of those, the statement unchanged', r => !isFalse(r.task) && translated.has(r.task) && !changesOf(gdp.find(g => g.task === r.task)!).length, true)
}

console.log('\n### Translation (gdp-wired)\n')
for (const [set, keep] of [['theorems', (t: string) => !isFalse(t)], ['false/', isFalse]] as const) {
  const rs = gdp.filter(r => keep(r.task))
  if (!rs.length) continue
  const tr = rs.filter(r => translated.has(r.task))
  console.log(`${set}: ${tr.length} of ${rs.length} translated; by directory:`, count(rs, r => `${r.task.split('/')[0]} ${translated.has(r.task) ? 'translated' : 'refused'}`).map(([k, v]) => `${k} ${v}`).join(', '))
  console.log('  statement changes among the translated:', count(tr, r => changesOf(r).join(' + ') || 'none'))
  console.log('  refused:', count(rs.filter(r => r.answer === 'unsupported'), r => why(r).replace(/: (F\d+_)?\S+: not structural.*/, '').replace(/F\d+_/g, '')))
  const nonstruct = rs.filter(r => /not structural/.test(why(r)))
  if (nonstruct.length) console.log('  recursion not taken, by function:', count(nonstruct, r => why(r).match(/F\d+_(\S+?):/)?.[1] ?? '?'))
  for (const r of rs.filter(r => r.answer === 'error')) console.log(`  error ${r.task}: ${why(r) || r.err?.slice(-200)}`)
}

const g = rows.filter(r => r.tool === 'gdp' && !isFalse(r.task) && translated.has(r.task))
if (g.length) {
  console.log('\n### gdp-wired on the translated theorems\n')
  console.log('answers:', count(g, r => r.answer))
  // (a law proven through the built-ins or its definitions unfolded, core/transfer.ts: its bridges and copy laws among
  // its lemmas, counted apart from the lemmas of the law said through them)
  const kind = (r: Row) => { const a = lastStage(r, 'answer'), through = (a?.through as string[] | undefined) ?? [], lemmas = ((a?.lemmas as string[] | undefined) ?? []).length - through.filter(t => !t.startsWith('unfolded')).length
    return `${str(a?.scheme).replace(/, through the law .*/, '').replace(/ of .*/, '')}${lemmas > 0 ? ' + lemmas' : ''}${through.length ? ' (through the built-ins or unfolded)' : ''}` }
  console.log('proven by scheme kind:', count(g.filter(r => r.answer === 'proven'), kind))
  const solved = (tool: string) => new Set(rows.filter(r => r.tool === tool && !isFalse(r.task) && r.answer === 'proven').map(r => r.task))
  const mine = solved('gdp')
  for (const t of tools.filter(t => t !== 'gdp' && t !== 'gdptr')) {
    const o = solved(t)
    console.log(`vs ${t}: both ${[...mine].filter(x => o.has(x)).length}, gdp-wired only ${[...mine].filter(x => !o.has(x)).length}, ${t} only (among translated) ${[...o].filter(x => !mine.has(x) && translated.has(x)).length}`)
  }
  const anyOther = new Set(tools.filter(t => t !== 'gdp' && t !== 'gdptr').flatMap(t => [...solved(t)]))
  console.log(`translated, unproven by gdp-wired, proven by some other tool: ${g.filter(r => r.answer !== 'proven' && anyOther.has(r.task)).length}; by none: ${g.filter(r => r.answer !== 'proven' && !anyOther.has(r.task)).length}`)
  console.log(`gdp-wired proven and no other tool: ${[...mine].filter(t => !anyOther.has(t)).join(', ') || 'none'}`)
}

// Solved per directory, each tool (the theorems).
{
  const dirs = [...new Set(rows.filter(r => !isFalse(r.task)).map(r => r.task.split('/')[0]!))]
  console.log(`\n### Proven per directory\n\n| tool | ${dirs.map(d => `${d} (${new Set(rows.filter(r => r.task.startsWith(`${d}/`)).map(r => r.task)).size})`).join(' | ')} |\n| --- | ${dirs.map(() => '---').join(' | ')} |`)
  for (const tool of tools.filter(t => t !== 'gdptr')) console.log(`| ${names[tool]} | ${dirs.map(d => rows.filter(r => r.tool === tool && r.task.startsWith(`${d}/`) && r.answer === 'proven').length).join(' | ')} |`)
  console.log(`| gdp-wired: translated | ${dirs.map(d => [...translated].filter(t => t.startsWith(`${d}/`)).length).join(' | ')} |`)
}
