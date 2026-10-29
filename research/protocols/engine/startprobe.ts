// The engine's start check alone, per protocol: each round-0 cube's start goal, until the first goal is asked.
//   GDP_GOAL_TRACE=1 bun research/protocols/engine/startprobe.ts [id]
import {inferLaws} from '../../../core/infer.ts'
import {protocols} from '../models.ts'
for (const p of protocols.filter(q => !process.argv[2] || q.id === process.argv[2])) {
  const r: any = p.make(), t0 = performance.now()
  inferLaws(r, p.laws(r), [], {ms: Number(process.env.MS ?? 60000), progress: (phase: string, info: any) => {
    if (phase === 'join start') console.log(p.id, JSON.stringify(info))
    if (phase === 'join goal') { console.log(p.id, 'first goal at', Math.round(performance.now() - t0)); process.exit(0) } }})
}
