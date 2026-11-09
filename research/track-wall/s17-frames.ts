// Section 17 frame probe: for each operation and each of the two helpers, the step goal's post counts (`c#`, bodies with the
// step's writes substituted by countedObligations) against their pre counts under the 15.7 frame rule (frameOk, the TS
// twin of Count.lean's FrameCuts): which pairs are frames with `when` = {op = o}, which with the other operations' flag
// conditions decided, and the simplified post body where no `when` makes a frame. Research only; nothing is admitted.
import {readFileSync} from 'node:fs'
import {all, same, x, n, type Law, type Machine, type E} from '../../core/machine.ts'
import type {Lin} from '../../core/solver.ts'
import {type Count, countedObligations} from '../../kernel/kernel.ts'
import {type FrameCut, frameOk, simpE, whenPath} from './frame-cut.ts'
const file = process.argv[2]!, p = JSON.parse(readFileSync(file, 'utf8'))
const opName = ['pick', 'copy', 'start', 'update_terms', 'become_leader', 'reconfig', 'send_config']
const text = (e: E): string => JSON.stringify(e).replace(/\{"op":"get","map":"([^"]+)","key":/g, '$1[').replace(/\{"op":"var","name":"([^"]+)"\}/g, '$1').replace(/\{"op":"const","value":(\d+)\}/g, '$1')
for (const tag of ['star', 'half']) {
  const law: Law = p.laws[p.targets[tag]]
  for (let op = 0; op < 7; op++) {
    const m: Machine = {...p.m, assume: all(...(p.m.assume ? [p.m.assume] : []), same(x('op'), n(op)))}
    const [, step] = countedObligations(m, p.laws, {}, p.targets[tag])
    const decls = step!.decls, counts: Count[] = decls.map(d => ({v: d.map, key: d.key, below: d.below, body: d.body}))
    const read = new Set<string>(JSON.stringify(law.holds).match(/"map":"([^"]+)"/g)?.map(s => s.slice(7, -1)) ?? [])
    const w0: Lin[] = [{op: 1, 1: -op}, {op: -1, 1: op}]
    const rows: string[] = []
    for (const c of [...read]) {
      const post = `${c}#`, f: FrameCut = {when: w0, post, pre: c}
      const ok0 = frameOk(counts, f)
      const d = counts.find(k => k.v === post)!
      const body = simpE(d.body, whenPath(f), d.key), below = simpE(d.below, whenPath(f), d.key)
      rows.push(`${c}: frame(op=${op})=${ok0}${ok0 ? '' : ` post.below=${text(below).slice(0, 120)} post.body=${text(body).slice(0, 420)}`}`)
    }
    console.log(`S17F ${tag} op${op} ${opName[op]} goal=${step!.goal.name} hyps=${step!.goal.hyps.length} decls=${decls.length} counts_read=${[...read].join(',')}\n  ${rows.join('\n  ')}`)
  }
}
