// Terms and conditions as Lean.Kern data (Kernel.lean's E and C): the one printer the exporters use and the
// conformance test (core/conformance.test.ts) checks against Lean's own evalE and evalC. Variables and maps are
// numbered by their place in `vars` and `maps`; a flag is the variable ?flag read as `= 1` (Progress.lean inlines it).
// A name with no number fails here, never as a malformed index in the Lean text.
import {type C, type E, unreachable} from '../core/machine.ts'

export function leanTerms(vars: readonly string[], maps: readonly string[], where: string) {
  const ix = (name: string) => { const j = vars.indexOf(name); if (j < 0) throw new Error(`${where}: no variable for ${name}`); return j }
  const mx = (name: string) => { const j = maps.indexOf(name); if (j < 0) throw new Error(`${where}: no map for ${name}`); return j }
  const e = (t: E): string => {
    switch (t.op) {
      case 'var': return `.var ${ix(t.name)}`
      case 'const': return `.const ${t.value}`
      case 'mul': return `.mul ${t.k} (${e(t.a)})`
      case 'add': case 'sub': case 'min': case 'max': case 'prod': return `.${t.op} (${e(t.a)}) (${e(t.b)})`
      case 'if': return `.ite (${c(t.c)}) (${e(t.then)}) (${e(t.else)})`
      case 'get': return `.get ${mx(t.map)} (${e(t.key)})`
      default: return unreachable(t)
    }
  }
  const c = (t: C): string => {
    switch (t.op) {
      case '<=': return `.le (${e(t.a)}) (${e(t.b)})`
      case '<': return `.lt (${e(t.a)}) (${e(t.b)})`
      case '=': return `.eq (${e(t.a)}) (${e(t.b)})`
      case 'not': return `.not (${c(t.x)})`
      case 'and': case 'or': {
        if (t.xs.length === 0) return t.op === 'and' ? '.le (.const 0) (.const 0)' : '.lt (.const 0) (.const 0)'
        return t.xs.map(c).reduceRight((acc, y) => `.${t.op} (${y}) (${acc})`)
      }
      case 'flag': return `.eq (.var ${ix(`?${t.name}`)}) (.const 1)`
      case 'all': throw new Error(`${where}: a quantified flag goes to Lean as a flag of its own, not a condition`)
      default: return unreachable(t)
    }
  }
  return {e, c}
}

// Terms and conditions as plain Lean over Nat (a recurrence's definition and its lemmas): each variable as the Lean
// expression `names` gives it.
export function leanSurface(names: Record<string, string>, where: string, get?: (map: string, key: E, e: (t: E) => string) => string) {
  const name = (n: string) => { const s = names[n]; if (s === undefined) throw new Error(`${where}: no Lean expression for ${n}`); return s }
  const e = (t: E): string => {
    switch (t.op) {
      case 'var': return name(t.name)
      case 'const': return String(t.value)
      case 'mul': return `(${t.k} * ${e(t.a)})`
      case 'add': return `(${e(t.a)} + ${e(t.b)})`
      case 'sub': return `(${e(t.a)} - ${e(t.b)})`
      case 'prod': return `(${e(t.a)} * ${e(t.b)})`
      case 'min': case 'max': return `(${t.op} ${e(t.a)} ${e(t.b)})`
      case 'if': return `(if ${c(t.c)} then ${e(t.then)} else ${e(t.else)})`
      case 'get': if (!get) throw new Error(`${where}: reads ${t.map}, a function or a map`); return get(t.map, t.key, e)
      default: return unreachable(t)
    }
  }
  const c = (t: C): string => {
    switch (t.op) {
      case '<=': return `${e(t.a)} ≤ ${e(t.b)}`
      case '<': return `${e(t.a)} < ${e(t.b)}`
      case '=': return `${e(t.a)} = ${e(t.b)}`
      case 'not': return `¬(${c(t.x)})`
      case 'and': case 'or': return t.xs.length === 0 ? (t.op === 'and' ? 'True' : 'False') : `(${t.xs.map(c).join(t.op === 'and' ? ' ∧ ' : ' ∨ ')})`
      case 'flag': case 'all': throw new Error(`${where}: takes no flag or quantifier`)
      default: return unreachable(t)
    }
  }
  return {e, c}
}
