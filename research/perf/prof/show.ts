// A condition or term as text, for reading goals.
import type {C, E} from '../../../core/machine.ts'
export const showE = (e: E): string => {
  switch (e.op) {
    case 'var': return e.name
    case 'const': return String(e.value)
    case 'add': return `(${showE(e.a)} + ${showE(e.b)})`
    case 'sub': return `(${showE(e.a)} ∸ ${showE(e.b)})`
    case 'mul': return `${e.k}·${showE(e.a)}`
    case 'prod': return `(${showE(e.a)} × ${showE(e.b)})`
    case 'min': return `min(${showE(e.a)}, ${showE(e.b)})`
    case 'max': return `max(${showE(e.a)}, ${showE(e.b)})`
    case 'if': return `if(${showC(e.c)}, ${showE(e.then)}, ${showE(e.else)})`
    case 'get': return `${e.map}[${showE(e.key)}]`
    default: return JSON.stringify(e)
  }
}
export const showC = (c: C): string => {
  switch (c.op) {
    case 'not': return `¬${showC(c.x)}`
    case 'and': return `(${c.xs.map(showC).join(' ∧ ')})`
    case 'or': return `(${c.xs.map(showC).join(' ∨ ')})`
    case 'all': return `∀${[c.key, ...(c.keys ?? [])].join(',')}. ${showC(c.c)}`
    case 'flag': return `flag ${c.name}`
    case '<': return `${showE(c.a)} < ${showE(c.b)}`
    case '<=': return `${showE(c.a)} ≤ ${showE(c.b)}`
    case '=': return `${showE(c.a)} = ${showE(c.b)}`
    default: return JSON.stringify(c)
  }
}
