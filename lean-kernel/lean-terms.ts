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
