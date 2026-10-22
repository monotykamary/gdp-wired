// A kernel goal (kernel.ts's Goal: hypotheses that can't hold together) to and from JSON, and as SMT-LIB.
// The JSON is hash-consed: a step's terms are shared objects (a state read by many hypotheses), so every object is
// written once, `{"#": n}` standing for the n-th; reading builds the same sharing back (the prover memoizes by object).
// The SMT-LIB states the kernel's reading of the goal: every name a natural (variables, map cells), ∸ truncating,
// `if`/min/max as ite, a map read as an uninterpreted function of its key; a named node read twice is a define-fun.
import type {C, E} from '../../core/machine.ts'
import type {Goal} from '../../kernel/kernel.ts'

export function dumpGoal(goal: Goal): string {
  const ids = new Map<object, number>(), nodes: unknown[] = []
  const enc = (x: unknown): unknown => {
    if (x === null || typeof x !== 'object') return x
    const had = ids.get(x as object)
    if (had !== undefined) return {'#': had}
    if (Array.isArray(x)) return x.map(enc)
    const out: Record<string, unknown> = {}
    for (const [key, val] of Object.entries(x)) out[key] = enc(val)
    const id = nodes.length
    nodes.push(out)
    ids.set(x as object, id)
    return {'#': id}
  }
  const hyps = goal.hyps.map(enc)
  return JSON.stringify({name: goal.name, nodes, hyps})
}

export function loadGoal(text: string): Goal {
  const raw = JSON.parse(text) as {name: string, nodes: Record<string, unknown>[], hyps: {'#': number}[]}
  const built: unknown[] = []
  const dec = (x: unknown): unknown => {
    if (x === null || typeof x !== 'object') return x
    if (Array.isArray(x)) return x.map(dec)
    const ref = (x as {'#'?: number})['#']
    if (ref !== undefined && Object.keys(x).length === 1) return built[ref]
    const out: Record<string, unknown> = {}
    for (const [key, val] of Object.entries(x)) out[key] = dec(val)
    return out
  }
  // Nodes are written children first (a node's id comes after its parts'), so one pass in order builds them.
  for (const n of raw.nodes) built.push(dec(n))
  return {name: raw.name, hyps: raw.hyps.map(h => built[h['#']] as C)}
}

const sym = (name: string) => `|${name.replace(/[|\\]/g, '_')}|`
const num = (n: number) => (n < 0 ? `(- ${-n})` : `${n}`)

export function toSmt(goal: Goal): string {
  const vars = new Set<string>(), maps = new Set<string>(), refs = new Map<object, number>()
  const count = (t: E | C): void => {
    const n = (refs.get(t) ?? 0) + 1
    refs.set(t, n)
    if (n > 1) return
    switch (t.op) {
      case 'var': vars.add(t.name); return
      case 'const': return
      case 'mul': return count(t.a)
      case 'get': maps.add(t.map); return count(t.key)
      case 'if': return (count(t.c), count(t.then), count(t.else))
      case 'add': case 'sub': case 'min': case 'max': case 'prod': return (count(t.a), count(t.b))
      case '<': case '<=': case '=': return (count(t.a), count(t.b))
      case 'and': case 'or': return t.xs.forEach(count)
      case 'not': return count(t.x)
      case 'flag': case 'all': throw new Error(`a goal with ${t.op} (inlined or closed before the kernel sees a goal)`)
    }
  }
  goal.hyps.forEach(count)
  const defs: string[] = [], named = new Map<object, string>()
  const isC = (t: E | C) => ['<', '<=', '=', 'and', 'or', 'not', 'flag', 'all'].includes(t.op)
  const go = (t: E | C): string => {
    const had = named.get(t)
    if (had) return had
    const body = text(t)
    if ((refs.get(t) ?? 0) > 1 && t.op !== 'var' && t.op !== 'const') {
      const n = `|n${named.size}|`
      defs.push(`(define-fun ${n} () ${isC(t) ? 'Bool' : 'Int'} ${body})`)
      named.set(t, n)
      return n
    }
    return body
  }
  const text = (t: E | C): string => {
    switch (t.op) {
      case 'var': return sym(t.name)
      case 'const': return num(t.value)
      case 'mul': return `(* ${num(t.k)} ${go(t.a)})`
      case 'prod': return `(* ${go(t.a)} ${go(t.b)})`
      case 'add': return `(+ ${go(t.a)} ${go(t.b)})`
      case 'sub': { const a = go(t.a), b = go(t.b); return `(ite (<= ${b} ${a}) (- ${a} ${b}) 0)` }
      case 'min': { const a = go(t.a), b = go(t.b); return `(ite (<= ${a} ${b}) ${a} ${b})` }
      case 'max': { const a = go(t.a), b = go(t.b); return `(ite (<= ${a} ${b}) ${b} ${a})` }
      case 'if': return `(ite ${go(t.c)} ${go(t.then)} ${go(t.else)})`
      case 'get': return `(${sym(`map ${t.map}`)} ${go(t.key)})`
      case '<': case '<=': case '=': return `(${t.op} ${go(t.a)} ${go(t.b)})`
      case 'and': return t.xs.length ? `(and ${t.xs.map(go).join(' ')})` : 'true'
      case 'or': return t.xs.length ? `(or ${t.xs.map(go).join(' ')})` : 'false'
      case 'not': return `(not ${go(t.x)})`
      case 'flag': case 'all': throw new Error(t.op)
    }
  }
  const asserts = goal.hyps.map(h => `(assert ${go(h)})`)
  const decls = [...vars].sort().flatMap(n => [`(declare-fun ${sym(n)} () Int)`, `(assert (<= 0 ${sym(n)}))`])
  // A map's every cell is a natural: stated at each key the goal reads (the kernel's leaf reads no other cell).
  const cells = [...refs.keys()].filter((t): t is Extract<E, {op: 'get'}> => (t as E).op === 'get').map(t => `(assert (<= 0 ${go(t)}))`)
  const mapDecls = [...maps].sort().map(m => `(declare-fun ${sym(`map ${m}`)} (Int) Int)`)
  return [`; ${goal.name}: ${goal.hyps.length} hypotheses, the kernel's reading (unsat = the goal holds)`, '(set-logic ALL)', ...decls, ...mapDecls, ...defs, ...cells, ...asserts, '(check-sat)', ''].join('\n')
}
