// The experiment's tables from its run directories:
//   bun research/table/summary.ts chc <run dir>            (classes: runs/modal/chc2/gap-v020.json)
//   bun research/table/summary.ts term <run dir> [<run dir>...]   (classes: research/table/jobs/term-tasks.json)
import {readFileSync} from 'node:fs'

const [kind, ...dirs] = process.argv.slice(2)
type Job = {name: string, code: number, seconds: number, out: string, err: string}
const jobs: Job[] = dirs.flatMap(d => readFileSync(`${d}/results.jsonl`, 'utf8').split('\n').filter(Boolean).map(l => JSON.parse(l) as Job))
const resultOf = (j: Job): Record<string, any> | undefined => {
  for (const l of j.out.split('\n').reverse()) { if (!l.startsWith('{')) continue; try { const x = JSON.parse(l); if (x.stage === 'result') return x } catch { /* partial line */ } }
  return undefined
}
const lastStage = (j: Job): string => { for (const l of j.out.split('\n').reverse()) { if (!l.startsWith('{')) continue; try { return JSON.parse(l).stage } catch { /* partial */ } } return 'none' }
const median = (xs: number[]) => { if (!xs.length) return NaN; const s = [...xs].sort((a, b) => a - b); return s.length % 2 ? s[(s.length - 1) / 2]! : (s[s.length / 2 - 1]! + s[s.length / 2]!) / 2 }
const pct = (xs: number[], p: number) => { if (!xs.length) return NaN; const s = [...xs].sort((a, b) => a - b); return s[Math.min(s.length - 1, Math.floor(p * s.length))]! }
const row = (cells: (string | number)[]) => `| ${cells.join(' | ')} |`

if (kind === 'chc') {
  const gap = JSON.parse(readFileSync('runs/modal/chc2/gap-v020.json', 'utf8')) as Record<string, {class: string, outside?: {cls: string, bools: number, linear: number}[]}>
  const by = new Map<string, {job: Job, r?: Record<string, any>}[]>()
  for (const j of jobs) { const c = gap[j.name]?.class ?? '?'; by.set(c, [...(by.get(c) ?? []), {job: j, r: resultOf(j)}]) }
  const levels = ['L0', 'L1', 'L2'] as const
  const first = (r: Record<string, any> | undefined, f: (lv: string) => boolean) => { if (!r) return 'no result'; for (const lv of levels) if (f(lv)) return lv; return 'none' }
  console.log('Recovery of Spacer\'s invariant, by its class (L0 = Q1+Q2, L1 = + Q5 one atom, L2 = + Q5 two atoms)\n')
  console.log(row(['class', 'tasks', 'result', 'on samples: L0', 'L1', 'L2', 'none', 'inductive (Houdini): L0', 'L1', 'L2', 'none', 'safe (solves the task): L0', 'L1', 'L2']))
  console.log(row(Array.from({length: 14}, () => '---')))
  const all: {job: Job, r?: Record<string, any>}[] = []
  const order = [...by.keys()].sort((a, b) => by.get(b)!.length - by.get(a)!.length)
  const line = (name: string, xs: {job: Job, r?: Record<string, any>}[]) => {
    const rs = xs.map(x => x.r)
    const onS = rs.map(r => first(r, lv => r!.recover?.[lv] === 'yes'))
    const ind = rs.map(r => first(r, lv => r!.houdini?.[lv]?.impliesSpacer === 'yes'))
    const safe = rs.map(r => first(r, lv => r!.houdini?.[lv]?.safe === 'yes'))
    const c = (xs: string[], v: string) => xs.filter(x => x === v).length
    console.log(row([name, xs.length, rs.filter(Boolean).length, c(onS, 'L0'), c(onS, 'L1'), c(onS, 'L2'), c(onS, 'none'), c(ind, 'L0'), c(ind, 'L1'), c(ind, 'L2'), c(ind, 'none'), c(safe, 'L0'), c(safe, 'L1'), c(safe, 'L2')]))
  }
  for (const c of order) { line(c, by.get(c)!); all.push(...by.get(c)!) }
  line('all', all)
  const rs = all.map(x => x.r).filter(Boolean) as Record<string, any>[]
  console.log(`\nno result line: ${all.filter(x => !x.r).length} (by last stage: ${JSON.stringify(Object.entries(all.filter(x => !x.r).reduce((a: Record<string, number>, x) => { const s = `${lastStage(x.job)} code ${x.job.code}`; a[s] = (a[s] ?? 0) + 1; return a }, {})))}); errors: ${JSON.stringify(Object.entries(rs.filter(r => r.error).reduce((a: Record<string, number>, r) => { const s = String(r.error).slice(0, 50); a[s] = (a[s] ?? 0) + 1; return a }, {})))}`)
  // the disjunctions: which level first, by the shape gap.py gives their clauses
  const dis = by.get('a disjunction of three or more') ?? []
  const shape = (name: string) => {
    const o = (gap[name]?.outside ?? []).filter(x => x.cls === 'a disjunction of three or more')
    if (o.some(x => x.linear >= 3)) return 'three or more linear literals'
    if (o.some(x => x.linear === 2)) return 'two linear literals beside yes/no values'
    return 'yes/no values beside at most one linear literal'
  }
  console.log('\nThe 154 disjunctions of three or more literals, by the first level whose Houdini-kept relations imply Spacer\'s invariant:\n')
  console.log(row(['shape (gap.py)', 'tasks', 'L0', 'L1 (one atom)', 'L2 (two atoms)', 'more (none of these)', 'no result']))
  console.log(row(Array.from({length: 7}, () => '---')))
  const groups = new Map<string, typeof dis>()
  for (const x of dis) { const s = shape(x.job.name); groups.set(s, [...(groups.get(s) ?? []), x]) }
  for (const [s, xs] of [...groups, ['all', dis] as const]) {
    const f = xs.map(x => first(x.r, lv => x.r!.houdini?.[lv]?.impliesSpacer === 'yes'))
    console.log(row([s, xs.length, ...['L0', 'L1', 'L2', 'none', 'no result'].map(v => f.filter(y => y === v).length)]))
  }
  // sizes, false positives, costs
  const preds = rs.flatMap(r => (r.table?.preds ?? []) as Record<string, any>[])
  console.log(`\npredicates ${preds.length}; rows (distinct sampled states) median ${median(preds.map(p => p.rows))}, p90 ${pct(preds.map(p => p.rows), 0.9)}, max ${Math.max(...preds.map(p => p.rows))}; predicates with no row ${preds.filter(p => !p.rows).length}`)
  for (const lv of levels) {
    const cols = preds.map(p => p.cols?.[lv] ?? 0), rel = preds.map(p => p[lv] ?? 0)
    console.log(`${lv}: columns per predicate median ${median(cols)}, max ${Math.max(...cols)}; relations per predicate median ${median(rel)}, max ${Math.max(...rel)}`)
  }
  for (const lv of levels) {
    const h = rs.map(r => r.houdini?.[lv]).filter((x: any) => x && !x.over)
    const cand = h.reduce((a: number, x: any) => a + x.candidates, 0), kept = h.reduce((a: number, x: any) => a + x.kept, 0)
    const dc = h.reduce((a: number, x: any) => a + x.droppedChecked, 0), di = h.reduce((a: number, x: any) => a + x.droppedImplied, 0)
    console.log(`Houdini ${lv}: ${h.length} tasks finished (${rs.filter(r => r.houdini?.[lv]?.over).length} out of time); relations ${cand}, kept ${kept}, dropped ${cand - kept} (${(100 * (cand - kept) / cand).toFixed(1)}%); of ${dc} dropped ones checked, Spacer's invariant implies ${di}; unknown checks ${h.reduce((a: number, x: any) => a + x.unknowns, 0)}`)
  }
  const secs = all.map(x => x.job.seconds)
  console.log(`\nwall per task (s): median ${median(secs)}, p90 ${pct(secs, 0.9)}, max ${Math.max(...secs)}, sum ${secs.reduce((a, b) => a + b, 0).toFixed(1)}`)
  for (const [k, f] of [['sample', (r: any) => r.sample?.ms], ['table + queries', (r: any) => r.table?.ms], ['Houdini L0', (r: any) => r.houdini?.L0?.ms], ['Houdini L1', (r: any) => r.houdini?.L1?.ms], ['Houdini L2', (r: any) => r.houdini?.L2?.ms]] as const) {
    const v = rs.map(f).filter((x: unknown) => typeof x === 'number') as number[]
    console.log(`${k} (ms): median ${median(v)}, p90 ${pct(v, 0.9)}, max ${Math.max(...v)}`)
  }
} else if (kind === 'term') {
  const cls = JSON.parse(readFileSync('research/table/jobs/term-tasks.json', 'utf8')) as {its: Record<string, string>, sv: Record<string, string>}
  const classOf = (n: string) => cls.its[n] ?? cls.sv[n] ?? '?'
  const by = new Map<string, {job: Job, r?: Record<string, any>}[]>()
  for (const j of jobs) { const c = `${cls.sv[j.name] ? 'SV' : 'ITS'}: ${classOf(j.name)}`; by.set(c, [...(by.get(c) ?? []), {job: j, r: resultOf(j)}]) }
  console.log(row(['class (failures.ts)', 'tasks', 'result', 'table rank verified (terminates)', 'KoAT2 terminates (here)', 'both', 'table only', 'KoAT2 only', 'components with no sampled turn', 'KoAT2 MPRFs', 'within the columns', 'same as one found here']))
  console.log(row(Array.from({length: 12}, () => '---')))
  const all: {job: Job, r?: Record<string, any>}[] = []
  const line = (name: string, xs: {job: Job, r?: Record<string, any>}[]) => {
    const rs = xs.map(x => x.r).filter(Boolean) as Record<string, any>[]
    const t = (r: any) => r.answer === 'terminates', k = (r: any) => r.koat?.answer === 'terminates'
    const comps = rs.flatMap(r => r.components ?? [])
    console.log(row([name, xs.length, rs.length, rs.filter(t).length, rs.filter(k).length, rs.filter(r => t(r) && k(r)).length, rs.filter(r => t(r) && !k(r)).length, rs.filter(r => !t(r) && k(r)).length,
      `${comps.filter((c: any) => !c.sampled).length} of ${comps.length}`, comps.reduce((a: number, c: any) => a + c.koat.mprfs, 0), comps.reduce((a: number, c: any) => a + c.koat.withinColumns, 0), comps.reduce((a: number, c: any) => a + c.koat.sameAsOurs, 0)]))
  }
  for (const c of [...by.keys()].sort()) { line(c, by.get(c)!); all.push(...by.get(c)!) }
  line('all', all)
  const rs = all.map(x => x.r).filter(Boolean) as Record<string, any>[]
  console.log(`\nno result line: ${all.filter(x => !x.r).length} (${JSON.stringify(Object.entries(all.filter(x => !x.r).reduce((a: Record<string, number>, x) => { const s = `${lastStage(x.job)} code ${x.job.code}`; a[s] = (a[s] ?? 0) + 1; return a }, {})))}); errors: ${JSON.stringify(Object.entries(rs.filter(r => r.error).reduce((a: Record<string, number>, r) => { const s = String(r.error).slice(0, 60); a[s] = (a[s] ?? 0) + 1; return a }, {})))}`)
  const comps = rs.flatMap(r => r.components ?? []) as Record<string, any>[]
  const ratio = comps.flatMap(c => Object.values(c.columns as Record<string, string>).map(s => s.split('/').map(Number) as [number, number]))
  console.log(`locations in components: ${ratio.length}; columns kept / arguments: ${ratio.reduce((a, [x]) => a + x, 0)} / ${ratio.reduce((a, [, y]) => a + y, 0)}`)
  console.log(`rank candidates refused by Z3: ${comps.reduce((a, c) => a + c.refused, 0)}; counterexample rows added: ${comps.reduce((a, c) => a + c.cexRows, 0)}; ranks accepted: ${comps.reduce((a, c) => a + c.found.length, 0)} (${comps.reduce((a, c) => a + c.found.filter((f: any) => f.withInv).length, 0)} needing the invariants)`)
  const secs = all.map(x => x.job.seconds)
  console.log(`wall per task (s): median ${median(secs)}, p90 ${pct(secs, 0.9)}, max ${Math.max(...secs)}, sum ${secs.reduce((a, b) => a + b, 0).toFixed(1)}`)
  for (const [k, f] of [['sample', (r: any) => r.sample?.ms], ['invariants', (r: any) => r.invariants?.ms], ['rank', (r: any) => r.rank?.ms], ['KoAT2 (s)', (r: any) => r.koat?.seconds]] as const) {
    const v = rs.map(f).filter((x: unknown) => typeof x === 'number') as number[]
    console.log(`${k}: median ${median(v)}, p90 ${pct(v, 0.9)}, max ${Math.max(...v)}`)
  }
}
