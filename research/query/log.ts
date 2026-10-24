// A preload (`bun --preload ./research/query/log.ts ...`, or BUN_OPTIONS for every bun process a run starts): each root
// query of the kernel's searches (kernel/prove.ts's grow, kernel/cdcl.ts's runs) as one JSON line in $GDP_QUERY_LOG: its
// kind (grow, cdcl: a tree wanted; model: only a model), the goal's name and hypotheses, wall ms, counted work (core/
// solver.ts's work.n), the outcome, and CDCL's counters over it. Research tooling, outside the library.
import {appendFileSync} from 'node:fs'
import {queryHook} from '../../kernel/prove.ts'
import {cdclStats} from '../../kernel/cdcl.ts'
import {costs} from '../../core/solver.ts'

const file = process.env.GDP_QUERY_LOG
if (file) {
  let buf: string[] = [], last = performance.now()
  const flush = () => { if (buf.length) { appendFileSync(file, buf.join('')); buf = [] } last = performance.now() }
  const keys = ['decisions', 'conflicts', 'nodes', 'leaves', 'runs'] as const
  let snap: number[] = [], csnap: Record<string, number> = {}
  const take = () => { snap = keys.map(k => cdclStats[k]); csnap = {...costs} }
  take()
  queryHook.on = q => {
    const now = keys.map(k => cdclStats[k]), c: Record<string, number> = {}
    for (const [k, x] of Object.entries(costs)) if (x !== (csnap[k] ?? 0)) c[k] = x - (csnap[k] ?? 0)
    const out = q.out, outcome = 'tree' in out ? 'tree' : out.stuck
    buf.push(JSON.stringify({pid: process.pid, kind: q.kind, name: q.goal.name, hyps: q.goal.hyps.length, ms: Math.round(q.ms * 100) / 100, work: q.work, outcome, ...('tree' in out ? {} : {why: out.why?.slice(0, 40)}),
      ...Object.fromEntries(keys.map((k, i) => [k, now[i]! - snap[i]!]).filter(([, x]) => x)), ...(Object.keys(c).length ? {c} : {})}) + '\n')
    take()
    if (buf.length > 200 || performance.now() - last > 250) flush()
  }
  process.on('exit', flush)
}
