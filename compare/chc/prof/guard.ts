import {readFileSync} from 'node:fs'
import {parseChc, type Sx} from '../chc.ts'
import {plan} from '../translate.ts'
const chc = parseChc(readFileSync(process.argv[2]!, 'utf8'))
const atoms = (s: Sx): number => typeof s === 'string' ? 0 : ['<=', '>=', '<', '>', '='].includes(s[0] as string) && !(s[0] === '=' && false) ? 1 + s.slice(1).reduce<number>((n, x) => n + atoms(x), 0) : s.slice(1).reduce<number>((n, x) => n + atoms(x), 0)
const size = (s: Sx): number => typeof s === 'string' ? 1 : s.reduce<number>((n, x) => n + size(x), 0)
chc.clauses.forEach((c, j) => {
  const p = plan(c, chc.preds)
  const defs = [...p.bound.values()].filter(b => b.kind === 'def'), inputs = [...p.bound.values()].filter(b => b.kind === 'input')
  console.log(`clause ${j}: vars ${c.vars.size}, constraint conjuncts ${c.constraint.length}, defs ${defs.length}, inputs ${inputs.length}, guard conjuncts ${p.guard.length}, guard atoms ${p.guard.reduce((n, s) => n + atoms(s), 0)}, guard size ${p.guard.reduce((n, s) => n + size(s), 0)}, def size ${defs.reduce((n, d) => n + size((d as {sx: Sx}).sx), 0)}`)
  if (j === 1) for (const g of p.guard.slice(0, 12)) console.log('   ', JSON.stringify(g).slice(0, 220))
})
