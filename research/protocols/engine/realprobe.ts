// The engine's first rounds on one protocol, its goal trace (GDP_GOAL_TRACE=2 also prints each real counterexample's state).
//   GDP_GOAL_TRACE=2 MS=60000 bun research/protocols/engine/realprobe.ts <id> [rounds]
import {inferLaws} from '../../../core/infer.ts'
import {protocols} from '../models.ts'
const p = protocols.find(q => q.id === process.argv[2])!, r: any = p.make(), last = Number(process.argv[3] ?? 0)
inferLaws(r, p.laws(r), [], {ms: Number(process.env.MS ?? 60000), progress: (phase: string, info: any) => {
  if (phase === 'join goal' || (phase === 'join enumerated' && 'round' in info)) console.log(phase, JSON.stringify(info))
  if (phase === 'join enumerated' && info.round >= last) process.exit(0) }})
