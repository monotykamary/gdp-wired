// Isolate the finite pass on real reached states; no solver calls or proof claims.
import {readFileSync} from 'node:fs'
import {protocols} from '../protocols/ic3syn/models.ts'
import {type Law, type Machine, interpret} from '../../core/machine.ts'
import {smallOf} from '../../core/exists.ts'
import {finiteEvaluator, finiteHoudini} from '../../core/finite-houdini.ts'
import {withWall, queryHook} from '../../kernel/prove.ts'
const input = JSON.parse(readFileSync(process.argv[2]!, 'utf8')).beforeFinite as {machine: Machine, caller: Law[], candidates: Law[]}
if (!input) throw Error('missing pre-filter capture')
const source = protocols.find(p => p.id === 'mldr')!.make().machine
const start = performance.now(), samples = withWall(performance.now() + 90_000, () => smallOf(input.machine, source))
const setupMs = performance.now() - start
let queries = 0; queryHook.on = () => { queries++ }
for (const targeted of [false, true]) for (let repeat = 1; repeat <= 3; repeat++) {
 const dropped: {round: number, law: string}[] = [], rounds: unknown[] = [], checked = finiteEvaluator(input.machine), run = interpret(source)
 let currentRound = -1, roundFamily = [...input.caller, ...input.candidates], alive = input.candidates.slice(), finish: unknown
 const t = performance.now()
 const result = finiteHoudini(source, input.machine, input.caller, input.candidates, samples, {targeted, onDrop: d => {
  if (currentRound !== d.round) { currentRound = d.round; roundFamily = [...input.caller, ...alive] }
  if (!roundFamily.every(l => checked(l, d.params, d.pre) === true)) throw Error('invalid predecessor')
  if (checked(d.law, d.params, run.step(d.params, d.pre, d.request)) !== false) throw Error('no real post-state violation')
  alive = alive.filter(l => l !== d.law); dropped.push({round: d.round, law: d.law.name})
 }, onRound: row => rounds.push(row), onFinish: row => { finish = row }})
 console.log(JSON.stringify({targeted, repeat, setupMs, elapsedMs: performance.now() - t, finish, dropped, rounds, laws: result.map(l => l.name), queries}))
}
if (queries) throw Error('finite generation made a solver query')
