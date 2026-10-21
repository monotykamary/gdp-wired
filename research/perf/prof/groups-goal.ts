// Each groups law's root goal: hypotheses and their size, and the instances chosen (`bun groups-goal.ts`).
import {groupLaws, groups} from '../../../examples/groups.ts'
import {proveStepLaws, setProveDump} from '../../../kernel/prove.ts'
const r = groups(), m = r.machine
for (const [i, sl] of groupLaws().entries()) {
  const seen: {hyps: number, chars: number}[] = []
  setProveDump(goal => { seen.push({hyps: goal.hyps.length, chars: JSON.stringify(goal.hyps).length}) })
  const out = proveStepLaws(m, [], [sl])
  setProveDump(undefined)
  const inst = out.proof?.perStep?.[sl.name] ?? out.proof?.instances ?? {}
  console.log(JSON.stringify({law: i, roots: seen, instances: Object.fromEntries(Object.entries(inst).map(([n, ks]) => [n, ks.length]))}))
}
