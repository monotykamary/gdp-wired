// Where a datatype law's time goes: proveData on a law of examples/data.ts (`<law>`, or `<law>!` for its broken variant)
// with the prover's profile on, then the root goals by time (outcome, nodes, solver time). `GIVEN=1` gives the law the
// lemmas research/data/withlemma.ts lists (never what the corpus does). DATA_TRACE=1 and PROVE_TRACE=1 add the search's
// and the prover's lines. bun research/data/prof.ts <law> [ms]
import {profile} from '../../kernel/prove.ts'
import {laws, broken} from '../../examples/data.ts'
import {proveData, type DataLaw} from '../../core/data.ts'

const name = process.argv[2]!, isBroken = name.endsWith('!'), ms = Number(process.argv[3] ?? 120000)
const l = ((isBroken ? broken : laws) as Record<string, () => DataLaw>)[name.replace(/!$/, '')]!()
const given = process.env.GIVEN ? ((await import('./given.ts')).given[name] ?? []) : undefined
profile.on = true
const v = proveData(l, {ms, ...(given ? {lemmas: given} : {})})
console.log(JSON.stringify({law: v.law, proven: v.proven, checked: v.checked, ms: v.ms, scheme: v.scheme, lemmas: v.lemmas, tried: v.tried, goal: v.goal, stuck: v.stuck}))
const goals = [...profile.goals].sort((a, b) => b.ms - a.ms)
console.log(`${goals.length} root goals, ${Math.round(goals.reduce((s, g) => s + g.ms, 0))} ms, ${goals.filter(g => !g.proven).length} not proven; solver ${Math.round(profile.solveMs)} ms in ${profile.solves} calls, rows ${Math.round(profile.rowsMs)} ms`)
for (const g of goals.slice(0, Number(process.env.TOP ?? 40))) console.log(`${Math.round(g.ms).toString().padStart(7)} ms ${g.proven ? 'proven' : 'NOT   '} ${String(g.nodes).padStart(6)} nodes ${Math.round(g.solveMs).toString().padStart(6)} ms solve  ${g.name.slice(0, 160)}`)
