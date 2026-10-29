// The engine's small instance alone, per protocol: inferLaws with a short budget, its 'join small instance' event.
//   bun research/protocols/engine/smallprobe.ts [id]
import {inferLaws} from '../../../core/infer.ts'
import {protocols} from '../models.ts'
for (const p of protocols.filter(q => !process.argv[2] || q.id === process.argv[2])) {
  const r: any = p.make()
  inferLaws(r, p.laws(r), [], {ms: Number(process.env.MS ?? 20000), progress: (phase: string, info: any) => { if (phase === (process.env.CUBES === 'made' ? 'join made' : 'join cubes') && process.env.CUBES) { console.log(String(info.cubes).split(' | ').map((c: string) => c.replace(/every [^:]*: /, '')).join('\n')); process.exit(0) }
    if ((phase === 'join template' || phase === 'join view' || phase === 'join small domains') && process.env.CUBES) console.log(phase, JSON.stringify(info))
    if (phase === 'join small instance') { console.log(p.id, JSON.stringify(info)); if (process.env.EXIT) process.exit(0) } }})
}
