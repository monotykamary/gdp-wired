import type {C, E} from '../../core/machine.ts'
const pairOf = (e: E): [E, E] | undefined => (e.op === 'add' && e.a.op === 'prod' && e.a.a.op === 'add' ? [e.a.a.a, e.b] : undefined)
export const sE = (e: E): string => {
  switch (e.op) {
    case 'var': return e.name
    case 'const': return String(e.value)
    case 'add': { const p = pairOf(e); return p ? `<${sE(p[0])}, ${sE(p[1])}>` : `(${sE(e.a)} + ${sE(e.b)})` }
    case 'sub': return `(${sE(e.a)} ∸ ${sE(e.b)})`
    case 'min': case 'max': return `${e.op}(${sE(e.a)}, ${sE(e.b)})`
    case 'mul': return `${e.k}·${sE(e.a)}`
    case 'prod': return `${sE(e.a)}·${sE(e.b)}`
    case 'if': return `(if ${sC(e.c)} then ${sE(e.then)} else ${sE(e.else)})`
    case 'get': return `${e.map}[${sE(e.key)}]`
  }
}
export const sC = (c: C): string => {
  switch (c.op) {
    case '<': case '<=': case '=': return `${sE(c.a)} ${c.op} ${sE(c.b)}`
    case 'and': return `(${c.xs.map(sC).join(' ∧ ')})`
    case 'or': return `(${c.xs.map(sC).join(' ∨ ')})`
    case 'not': return `¬${sC(c.x)}`
    case 'flag': case 'all': return JSON.stringify(c)
  }
}
