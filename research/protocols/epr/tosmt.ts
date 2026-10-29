// A kernel goal (its hypotheses, naturals) as SMT-LIB 2: unsat iff the goal is proven. Maps are functions of their key.
import {readFileSync, writeFileSync} from 'node:fs'
const goal = JSON.parse(readFileSync(process.argv[2]!, 'utf8')), out = process.argv[3]!
const q = (s: string) => `|${s.replace(/\|/g, '_')}|`
const vars = new Set<string>(), fns = new Map<string, number>(), cells = new Set<string>()
const E = (e: any): string => {
  switch (e.op) {
    case 'var': vars.add(e.name); return q(e.name)
    case 'const': return String(e.value)
    case 'add': return `(+ ${E(e.a)} ${E(e.b)})`
    case 'sub': { const a = E(e.a), b = E(e.b); return `(ite (>= ${a} ${b}) (- ${a} ${b}) 0)` }
    case 'mul': return `(* ${e.k} ${E(e.a)})`
    case 'prod': return `(* ${E(e.a)} ${E(e.b)})`
    case 'min': { const a = E(e.a), b = E(e.b); return `(ite (<= ${a} ${b}) ${a} ${b})` }
    case 'max': { const a = E(e.a), b = E(e.b); return `(ite (>= ${a} ${b}) ${a} ${b})` }
    case 'if': return `(ite ${C(e.c)} ${E(e.then)} ${E(e.else)})`
    case 'get': { const args = e.args ? e.args.map(E) : [E(e.key)], name = `${e.map}/${args.length}`; fns.set(name, args.length); const t = `(${q(name)} ${args.join(' ')})`; cells.add(t); return t }
  }
  throw new Error('term ' + e.op)
}
const C = (c: any): string => {
  switch (c.op) {
    case '<': return `(< ${E(c.a)} ${E(c.b)})`
    case '<=': return `(<= ${E(c.a)} ${E(c.b)})`
    case '=': return `(= ${E(c.a)} ${E(c.b)})`
    case 'and': return c.xs.length ? `(and ${c.xs.map(C).join(' ')})` : 'true'
    case 'or': return c.xs.length ? `(or ${c.xs.map(C).join(' ')})` : 'false'
    case 'not': return `(not ${C(c.x)})`
  }
  throw new Error('condition ' + c.op)
}
const body = goal.hyps.map((h: any) => `(assert ${C(h)})`)
const lines = ['(set-logic QF_UFLIA)', ...[...vars].map(v => `(declare-fun ${q(v)} () Int)`), ...[...fns].map(([f, n]) => `(declare-fun ${q(f)} (${Array(n).fill('Int').join(' ')}) Int)`),
  ...[...vars].map(v => `(assert (>= ${q(v)} 0))`), ...[...cells].map(t => `(assert (>= ${t} 0))`), ...body, '(check-sat)']
writeFileSync(out, lines.join('\n') + '\n')
console.log(out, goal.hyps.length, 'hyps', vars.size, 'vars', cells.size, 'cells')
