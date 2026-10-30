// gen/laneA2: two replays of one dump (wodl.ts replay, each tree's decideLaw) compared goal by goal: the verdicts both
// decided that differ (proven against a model), and what each left undecided.
//   bun research/protocols/engine/agree.ts <base.txt> <new.txt>
import {readFileSync} from 'node:fs'

const rows = (f: string) => new Map(readFileSync(f, 'utf8').split('\n').filter(l => l.startsWith('{"at"')).map(l => JSON.parse(l)).map(o => [o.at as number, o as {dl: string, ms: number, law: string}]))
const [a, b] = process.argv.slice(2).map(rows) as [ReturnType<typeof rows>, ReturnType<typeof rows>]
let both = 0, differ = 0, onlyA = 0, onlyB = 0, msA = 0, msB = 0
for (const [k, x] of a) {
  const y = b.get(k)
  if (!y) continue
  msA += x.ms; msB += y.ms
  if (x.dl !== 'undecided' && y.dl !== 'undecided') { both++; if (x.dl !== y.dl) { differ++; console.log('DIFFER', k, x.dl, y.dl, x.law) } }
  else if (x.dl !== 'undecided') onlyA++
  else if (y.dl !== 'undecided') onlyB++
}
console.log(JSON.stringify({goals: a.size, compared: [...a.keys()].filter(k => b.has(k)).length, bothDecided: both, differ, decidedOnlyBase: onlyA, decidedOnlyNew: onlyB, msBase: Math.round(msA), msNew: Math.round(msB)}))
