// The names a depth-k goal reads once reduced, by kind: `bun research/bmc2/names.ts <task.smt2> <k>`
import {readFileSync} from 'node:fs'
import {parseChc} from '../../compare/chc/chc.ts'
import {build} from '../../compare/chc/translate.ts'
import {bmcGoal, fixed, reduce, relax} from '../../core/bmc.ts'
import type {C, E} from '../../core/machine.ts'
const b = build(parseChc(readFileSync(process.argv[2]!, 'utf8')))
const k = Number(process.argv[3])
const g = bmcGoal(b.rule.machine, [b.law], k), f = fixed(g.hyps)!, r = reduce(relax(f.hyps) ?? f.hyps)!
const names = new Map<string, number>()
const go = (x: C | E): void => { if (x.op === 'var') { names.set(x.name, (names.get(x.name) ?? 0) + 1); return } for (const v of Object.values(x)) if (v && typeof v === 'object') (Array.isArray(v) ? v : [v]).forEach(y => { if (y && typeof y === 'object' && 'op' in y) go(y as C) }) }
r.hyps.forEach(go)
const kinds = new Map<string, number>()
for (const n of names.keys()) { const kind = n.includes('~') ? `state~${n.split('~')[1]}` : n.includes('@') ? `input@${n.split('@')[1]}` : /^[xyc]/.test(n) ? 'input@1' : 'other:' + n; kinds.set(kind, (kinds.get(kind) ?? 0) + 1) }
console.log([...kinds].sort())
console.log('once', [...names].filter(([, c]) => c === 1).length, 'twice', [...names].filter(([, c]) => c === 2).length)
