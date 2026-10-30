// One port's law through proveRule with the search off (the runs that refute, then the kernel's proof), within a wall:
// where a law with "there exists" spends its time before the search starts.
//   bun [--cpu-prof] research/protocols/ic3syn/probe.ts <id> [wall ms]
import {proveRule} from '../../../core/dsl.ts'
import {withWall} from '../../../kernel/prove.ts'
import {protocols} from './models.ts'

const p = protocols.find(q => q.id === process.argv[2])!, wall = Number(process.argv[3] ?? 20_000)
const r: any = p.make(), laws = p.laws(r), t0 = performance.now()
const v: any = withWall(performance.now() + wall, () => proveRule(r, laws, {search: false}))
console.log(JSON.stringify({id: p.id, proven: v.proven, run: !!v.run, goal: v.goal, why: String(v.why ?? '').slice(0, 200), ms: Math.round(performance.now() - t0)}))
