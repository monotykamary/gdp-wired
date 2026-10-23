// The cone of influence of a CHC task's rule: `bun research/bmc2/cone.ts <task.smt2>...` prints the state values and how
// many the laws, the assumption and the precondition reach through the updates.
import {readFileSync} from 'node:fs'
import {parseChc} from '../../compare/chc/chc.ts'
import {build} from '../../compare/chc/translate.ts'
import type {C, E} from '../../core/machine.ts'
const vars = (x: C | E, out: Set<string>): Set<string> => { if (x.op === 'var') out.add(x.name); for (const y of Object.values(x)) if (y && typeof y === 'object') (Array.isArray(y) ? y : [y]).forEach(z => { if (z && typeof z === 'object' && 'op' in z) vars(z as C, out) }); return out }
for (const file of process.argv.slice(2)) {
  const m = build(parseChc(readFileSync(file, 'utf8'))).rule.machine, law = build(parseChc(readFileSync(file, 'utf8'))).law
  const live = new Set<string>(), todo = [...vars(law.holds, new Set()), ...(m.assume ? vars(m.assume, new Set()) : [])].filter(n => n in m.state)
  while (todo.length) { const n = todo.pop()!; if (live.has(n)) continue; live.add(n); todo.push(...[...vars(m.step.state?.[n] ?? {op: 'var', name: n}, new Set())].filter(x => x in m.state)) }
  console.log(file.split('/').pop(), Object.keys(m.state).length, live.size)
}
