// The counted search's first two phases alone (core/counts.ts: the small instances, then the engine's cubes on their
// rows), timed, for a CPU profile of where they spend (`bun --cpu-prof`; cpuprof.py reads the profile's top functions).
//   bun [--cpu-prof] research/protocols/engine/smallbench.ts consensus_wo_decide
import {guardLaws} from '../../../core/counts.ts'
import {smallOf} from '../../../core/exists.ts'
import {inferLaws} from '../../../core/infer.ts'
import {protocols} from '../ic3syn/models.ts'

const id = process.argv[2] ?? 'consensus_wo_decide'
const p = protocols.find(q => q.id === id)!, r: any = p.make(), m0 = r.machine, g = guardLaws(m0), m = {...m0, counts: {...m0.counts, ...g.counts}}
const caller = [...r.kindLaws(), ...p.laws(r)]
let t = performance.now()
const states = smallOf(m)
const tSmall = performance.now() - t
t = performance.now()
const cubes = inferLaws(m0, caller, [], {cubes: 2, ms: 15_000, first: {proven: false, checked: false}, rows: states.flatMap(({p: ps, sts}) => sts.map(st => ({params: ps, st})))}).found
console.log(JSON.stringify({id, states: states.map(s => s.sts.length), smallMs: Math.round(tSmall), cubes: cubes.length, cubesMs: Math.round(performance.now() - t)}))
