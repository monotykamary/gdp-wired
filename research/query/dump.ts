// A preload (`bun --preload ./research/query/dump.ts ...`): every root query of the kernel's searches as one JSON line in
// $DUMP_DIR/queries.jsonl (kind, name, hypotheses, wall ms, counted work, outcome), and the root goals past $DUMP_MIN
// hypotheses (default 150, at most $DUMP_MAX, 20,000) that ran out or took a second, written to $DUMP_DIR as JSON
// ({kind, ms, outcome, goal}), at most $DUMP_N (8) a process: research/query/wide-lab.ts's inputs. Research tooling.
import {appendFileSync, mkdirSync, writeFileSync} from 'node:fs'
import {queryHook} from '../../kernel/prove.ts'

const dir = process.env.DUMP_DIR, min = Number(process.env.DUMP_MIN ?? 150), max = Number(process.env.DUMP_MAX ?? 20_000), most = Number(process.env.DUMP_N ?? 8)
if (dir) {
  mkdirSync(dir, {recursive: true})
  let n = 0
  const seen = new Set<string>()
  queryHook.on = q => {
    const out = q.out, outcome = 'tree' in out ? 'tree' : out.stuck, h = q.goal.hyps.length
    appendFileSync(`${dir}/queries.jsonl`, JSON.stringify({kind: q.kind, name: q.goal.name.slice(0, 80), hyps: h, ms: Math.round(q.ms), work: q.work, outcome, why: 'tree' in out ? undefined : out.why?.slice(0, 60)}) + '\n')
    if (n >= most || h < min || h > max || (outcome === 'tree' && q.ms < 1_000) || seen.has(`${q.goal.name} ${h}`)) return
    seen.add(`${q.goal.name} ${h}`)
    writeFileSync(`${dir}/${process.pid}-${n++}.json`, JSON.stringify({kind: q.kind, ms: Math.round(q.ms), outcome, goal: q.goal}))
  }
}
