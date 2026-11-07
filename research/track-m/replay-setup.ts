import {readFileSync} from 'node:fs'
import {type Instances, countedObligations} from '../../kernel/kernel.ts'
import {walkOnce, x} from '../../core/machine.ts'
import {certFor} from '../../core/counts.ts'
import {seedCountWitnessFlags} from '../../core/count-witness-flags.ts'

export function prepareCaptured(file: string, input: string, mode: string) {
  const d = JSON.parse(readFileSync(file, 'utf8')), {m} = JSON.parse(readFileSync(input, 'utf8'))
  const ls = d.laws, index = ls.findIndex((l: any) => l.name === d.law), law = ls[index]
  let at: Instances = d.at
  if (mode.includes('flags')) {
    const used = new Set<string>()
    walkOnce(d.hyps, (o: any) => { if (o.op === 'var' && /^w\$\d+$/.test(o.name)) used.add(o.name) })
    const cert = certFor(d.base, d.decls, true, 1000)
    at = seedCountWitnessFlags(m, at, [{decls: d.decls, cert: {...cert, insts: cert.insts.filter(i => used.has(i.wit))}}])
  }
  if (mode.includes('own') && law.forall) at = {...at, [law.name]: [...at[law.name] ?? [], x(`${law.forall}#`), ...law.keys?.map(x) ?? []]}
  const rebuilt = countedObligations(m, ls, {[law.name]: at}, index).find(g => g.goal.name.endsWith('@step'))!.goal
  return {d, goal: mode === 'raw' ? d.goal : {name: d.goal.name, hyps: [...rebuilt.hyps, ...d.hyps.slice(d.base.hyps.length)]}}
}
