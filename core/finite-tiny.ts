// UNTRUSTED relative-CTI proposals, not a proof, finite cover, or drop decision.
// The consumer MUST independently check m.pre, ALL m.facts, the WHOLE current
// family, the source interpreter's enabled step, and each reported post-law. This module owns no
// solver/kernel policy and never extends the enclosing cooperative wall.
import {type C, type E, type Law, type Machine, type Request, type State, cpair, cunpair, walk} from './machine.ts'
import {checkWall, WallExpired} from './wall.ts'
type Env = Record<string, number>
type Term = {id: number, code: string, args: Term[], deps: number[], lo: number, hi: number, values?: number[], choice?: {c: Pred, a: Term, b: Term}}
type Pred = boolean | {op: 'atom', a: Term, b: Term, cmp: '<' | '<=' | '='} | {op: 'and', xs: Pred[]} | {op: 'or', xs: Pred[]} | {op: 'not', x: Pred}
type Slot = {name: string, key?: number, request?: boolean, values: number[]}
export type TinyFiniteOptions = {valueDomain?: readonly number[], postTargetPruning?: boolean}
export type TinyFiniteStatistics = {
  scope: {params: Env, scalarValues: number[], cellValues: number[], cells: Record<string, number[]>, inputValues: Record<string, number[]>, inputCells: Record<string, number[]>, binderValues: number[], postTargetPruning: boolean}
  completed: boolean, exhausted: boolean, timedOut: boolean, unsupported: string[], nodes: number, states: number, steps: number, scenarios: number, candidates: number, postStatePrunes: number, postRequestPrunes: number, ms: number
}
const unique = (xs: number[]) => [...new Set(xs)]
const conjunction = (xs: Pred[]): Pred => {
  if (xs.includes(false)) return false
  const ys = xs.filter(x => x !== true)
  return ys.length === 0 ? true : ys.length === 1 ? ys[0]! : {op: 'and', xs: ys}
}
const disjunction = (xs: Pred[]): Pred => {
  if (xs.includes(true)) return true
  const ys = xs.filter(x => x !== false)
  return ys.length === 0 ? false : ys.length === 1 ? ys[0]! : {op: 'or', xs: ys}
}
const negate = (x: Pred): Pred => typeof x === 'boolean' ? !x : x.op === 'not' ? x.x : {op: 'not', x}
const dependencyCache = new WeakMap<object, number[]>()
const depsOf = (p: Pred): number[] => {
  if (typeof p === 'boolean') return []
  checkWall('tiny dependencies')
  const hit = dependencyCache.get(p)
  if (hit) return hit
  const out = p.op === 'atom' ? unique([...p.a.deps, ...p.b.deps]) : p.op === 'not' ? depsOf(p.x) : unique(p.xs.flatMap(depsOf))
  dependencyCache.set(p, out); return out
}
const conjuncts = (c: C): C[] => c.op === 'and' ? c.xs.flatMap(conjuncts) : [c]
class Unsupported extends Error {}
// All code strings below are built from closed operators, numerical literals,
// and slot numbers. Source names and external function JS are never executable.
class Compiler {
  terms: Term[] = []
  flagConstants = new Map<string, boolean>()
  intern = new Map<string, Term>()
  reads = new Map<string, Term>()
  flags = new Map<string, Pred>()
  environmentKey(env: Env): string { return this.source.inputs.map(k => Object.hasOwn(env, k) ? `${k}:${env[k]!}` : k).join(';') }
  constructor(readonly source: Machine, readonly m: Machine, readonly p: Env, readonly slots: Slot[], readonly cells: Record<string, number[]>, readonly binders: number[]) {}
  term(code: string, args: Term[], lo: number, hi: number, deps = unique(args.flatMap(t => t.deps))): Term {
    if (!Number.isSafeInteger(lo) || !Number.isSafeInteger(hi)) throw new Unsupported('inexact arithmetic range')
    const key = code + ':' + args.map(a => a.id).join(',')
    let t = this.intern.get(key)
    if (!t) { t = {id: this.terms.length, code, args, lo, hi, deps, ...(hi - lo <= 16 ? {values: Array.from({length: hi - lo + 1}, (_, i) => lo + i)} : {})}; this.terms.push(t); this.intern.set(key, t) }
    return t
  }
  constant(n: number): Term { return this.term(String(n), [], n, n) }
  ref(t: Term): string { return `t${t.id}` }
  slot(i: number): Term { const vs = this.slots[i]!.values; return this.term(`v[${i}]`, [], Math.min(...vs), Math.max(...vs), [i]) }
  binary(op: E['op'], a: Term, b: Term): Term {
    checkWall('tiny arithmetic compile')
    const finish = (t: Term): Term => {
      if (a.values && b.values && a.values.length * b.values.length <= 256) t.values = unique(a.values.flatMap(x => b.values!.map(y => op === 'add' ? x + y : op === 'sub' ? Math.max(0, x - y) : op === 'prod' ? x * y : op === 'min' ? Math.min(x, y) : op === 'max' ? Math.max(x, y) : cpair(x, y)))).sort((x, y) => x - y)
      return t
    }
    const ar = this.ref(a), br = this.ref(b)
    if (a.lo === a.hi && b.lo === b.hi) {
      const x = a.lo, y = b.lo
      return this.constant(op === 'add' ? x + y : op === 'sub' ? Math.max(0, x - y) : op === 'prod' ? x * y : op === 'min' ? Math.min(x, y) : op === 'max' ? Math.max(x, y) : cpair(x, y))
    }
    if ((op === 'add' || op === 'sub') && b.hi === 0) return a
    if (op === 'add' && a.hi === 0) return b
    if (op === 'prod' && (a.hi === 0 || b.hi === 0)) return this.constant(0)
    if (op === 'prod' && b.lo === 1 && b.hi === 1) return a
    if (op === 'prod' && a.lo === 1 && a.hi === 1) return b
    if (op === 'add') return finish(this.term(`(${ar}+${br})`, [a, b], a.lo + b.lo, a.hi + b.hi))
    if (op === 'sub') return finish(this.term(`Math.max(0,${ar}-${br})`, [a, b], Math.max(0, a.lo - b.hi), Math.max(0, a.hi - b.lo)))
    if (op === 'prod') return finish(this.term(`(${ar}*${br})`, [a, b], a.lo * b.lo, a.hi * b.hi))
    if (op === 'min' || op === 'max') return finish(this.term(`Math.${op}(${ar},${br})`, [a, b], Math[op](a.lo, b.lo), Math[op](a.hi, b.hi)))
    throw new Unsupported('nonconstant tuple')
  }
  compare(cmp: '<' | '<=' | '=', a: Term, b: Term): Pred {
    checkWall('tiny comparison compile')
    if (cmp === '=') { if (a.id === b.id) return true; if (a.hi < b.lo || b.hi < a.lo) return false; if (a.lo === a.hi && b.lo === b.hi) return a.lo === b.lo }
    if (cmp === '<') { if (a.hi < b.lo) return true; if (a.lo >= b.hi) return false }
    if (cmp === '<=') { if (a.hi <= b.lo) return true; if (a.lo > b.hi) return false }
    if (a.choice) { const q = a.choice; return disjunction([conjunction([q.c, this.compare(cmp, q.a, b)]), conjunction([negate(q.c), this.compare(cmp, q.b, b)])]) }
    if (b.choice) { const q = b.choice; return disjunction([conjunction([q.c, this.compare(cmp, a, q.a)]), conjunction([negate(q.c), this.compare(cmp, a, q.b)])]) }
    return {op: 'atom', cmp, a, b}
  }
  // A numeric conditional keeps its condition's dependencies; the condition is
  // evaluated only once all of them are assigned (no guessed truth values).
  conditional(c: Pred, a: Term, b: Term): Term {
    if (typeof c === 'boolean') return c ? a : b
    if (a.id === b.id) return a
    if (a.lo === 1 && a.hi === 1 && b.lo === 0 && b.hi === 0 && c.op === 'atom') {
      if (c.cmp === '=' && c.a.lo === 0 && c.a.hi === 1 && c.b.lo === 1 && c.b.hi === 1) return c.a
      if (c.cmp === '<=' && c.a.lo === 1 && c.a.hi === 1 && c.b.lo === 0 && c.b.hi === 1) return c.b
    }
    const ds = unique([...depsOf(c), ...a.deps, ...b.deps]), used: Term[] = []
    const code = this.predicateCode(c, undefined, used)
    const out = this.term(`(${code}?${this.ref(a)}:${this.ref(b)})`, uniqueTerms([...used, a, b]), Math.min(a.lo, b.lo), Math.max(a.hi, b.hi), ds)
    out.choice = {c, a, b}
    if (a.values && b.values) out.values = unique([...a.values, ...b.values]).sort((x, y) => x - y)
    return out
  }
  expression(e: E, env: Env, post = false, stack: string[] = []): Term {
    checkWall('tiny compile expression')
    if (stack.length > 48) throw new Unsupported('recursive count/flag')
    switch (e.op) {
      case 'const': return this.constant(e.value)
      case 'var': {
        if (Object.hasOwn(env, e.name)) return this.constant(env[e.name]!)
        if (post && e.name in this.source.state) return this.expression(this.source.step.state?.[e.name] ?? e, env, false, stack)
        const i = this.slots.findIndex(s => s.key === undefined && s.name === e.name)
        if (i >= 0) return this.slot(i)
        throw new Unsupported(`free variable ${e.name}`)
      }
      case 'add': case 'sub': case 'prod': case 'min': case 'max': case 'tup': return this.binary(e.op, this.expression(e.a, env, post, stack), this.expression(e.b, env, post, stack))
      case 'mul': return this.binary('prod', this.constant(e.k), this.expression(e.a, env, post, stack))
      case 'proj': { const a = this.expression(e.a, env, post, stack); if (a.lo !== a.hi) throw new Unsupported('nonconstant projection'); return this.constant(cunpair(a.lo)[e.k]) }
      case 'if': {
        const c = this.condition(e.c, env, post, stack)
        if (typeof c === 'boolean') return this.expression(c ? e.then : e.else, env, post, stack)
        return this.conditional(c, this.expression(e.then, env, post, stack), this.expression(e.else, env, post, stack))
      }
      case 'get': {
        const key = this.expression(e.key, env, post, stack)
        if (key.lo !== key.hi) {
          if (!key.values && key.hi - key.lo > 256) throw new Unsupported('wide dynamic map key')
          if (key.values && key.values.length > 256) throw new Unsupported('many dynamic map keys')
          const keys = key.values ?? Array.from({length: key.hi - key.lo + 1}, (_, i) => key.lo + i)
          let out = this.read(e.map, keys.at(-1)!, env, post, stack)
          for (const k of keys.slice(0, -1).reverse()) { checkWall('tiny dynamic reads'); out = this.conditional(this.compare('=', key, this.constant(k)), this.read(e.map, k, env, post, stack), out) }
          return out
        }
        return this.read(e.map, key.lo, env, post, stack)
      }
    }
  }
  read(map: string, key: number, env: Env, post: boolean, stack: string[]): Term {
    checkWall('tiny compile read')
    const id = JSON.stringify([map, key, post, this.environmentKey(env)])
    const hit = this.reads.get(id)
    if (hit) return hit
    const value = this.readUncached(map, key, env, post, stack)
    this.reads.set(id, value)
    return value
  }
  readUncached(map: string, key: number, env: Env, post: boolean, stack: string[]): Term {
    const d = this.m.counts?.[map]
    if (d) {
      if (stack.includes(`count:${map}`)) throw new Unsupported('recursive count')
      const at = {...env, [d.j]: d.base ? Math.floor(key / d.base) : key, ...(d.lo && d.base ? {[d.lo]: key % d.base} : {})}
      const bound = this.expression(d.below, at, post, stack)
      if (bound.lo !== bound.hi || bound.hi > 16) throw new Unsupported('nonconstant/large count bound')
      let out = this.constant(0)
      for (let k = 0; k < bound.hi; k++) { checkWall('tiny count expansion'); out = this.binary('add', out, this.expression(d.body, {...at, [d.key]: k}, post, [...stack, `count:${map}`])) }
      return out
    }
    if (this.m.fns?.[map]) throw new Unsupported('external function')
    if (post && map in (this.source.maps ?? {})) {
      const w = this.source.step.maps?.[map]
      if (w && 'each' in w) return this.expression(w.value, {...env, [w.each]: key}, false, stack)
      if (w) return this.conditional(this.compare('=', this.expression(w.key, env, false, stack), this.constant(key)), this.expression(w.value, env, false, stack), this.read(map, key, env, false, stack))
    }
    const i = this.slots.findIndex(s => s.name === map && s.key === key)
    if (i >= 0) return this.slot(i)
    if (map in (this.source.maps ?? {})) return this.constant(this.source.maps![map]!)
    if (this.source.inputMaps?.includes(map)) return this.constant(0)
    throw new Unsupported(`unknown map ${map}`)
  }
  condition(c: C, env: Env, post = false, stack: string[] = []): Pred {
    checkWall('tiny compile predicate')
    if (stack.length > 48) throw new Unsupported('recursive count/flag')
    switch (c.op) {
      case '<': case '<=': case '=': return this.compare(c.op, this.expression(c.a, env, post, stack), this.expression(c.b, env, post, stack))
      case 'not': return negate(this.condition(c.x, env, post, stack))
      case 'and': case 'or': {
        const xs: Pred[] = []
        for (const x of c.xs) { const p = this.condition(x, env, post, stack); if (p === (c.op === 'or')) return p; xs.push(p) }
        return c.op === 'and' ? conjunction(xs) : disjunction(xs)
      }
      case 'flag': {
        if (this.flagConstants.has(c.name)) return this.flagConstants.get(c.name)!
        const f = this.source.step.flags?.[c.name]
        if (!f || stack.includes(`flag:${c.name}`)) throw new Unsupported('unknown/recursive flag')
        const id = JSON.stringify([c.name, this.environmentKey(env)])
        let value = this.flags.get(id)
        if (value === undefined) { value = this.condition(f, env, false, [...stack, `flag:${c.name}`]); this.flags.set(id, value) }
        return value
      }
      case 'all': return conjunction(bindings([c.key, ...c.keys ?? []], this.binders, env).map(at => this.condition(c.c, at, post, stack)))
    }
  }
  predicateCode(p: Pred, rank: number[] | undefined, used: Term[], polarity = true): string {
    checkWall('tiny predicate code')
    if (typeof p === 'boolean') return String(p === polarity)
    if (p.op === 'not') return this.predicateCode(p.x, rank, used, !polarity)
    if (p.op === 'and' || p.op === 'or') return '(' + p.xs.map(x => this.predicateCode(x, rank, used, polarity)).join((p.op === 'and') === polarity ? '&&' : '||') + ')'
    used.push(p.a, p.b)
    const ds = unique([...p.a.deps, ...p.b.deps]), ready = rank ? Math.max(-1, ...ds.map(i => rank[i]!)) + 1 : 0
    const test = `(${this.ref(p.a)}${p.cmp === '=' ? '===' : p.cmp}${this.ref(p.b)})`
    return `(${rank && ready > 0 ? `d<${ready}||` : ''}${polarity ? test : '!' + test})`
  }
  compileValues(values: Term[], order?: number[]): (v: number[], depth?: number) => number[] {
    checkWall('tiny transition code')
    const rank = order ? this.slots.map((_, i) => order.indexOf(i)) : undefined
    const seen = new Set<number>(), lines: string[] = []
    let chars = 0
    const emit = (t: Term): void => {
      checkWall('tiny transition terms')
      if (seen.has(t.id)) return
      seen.add(t.id); t.args.forEach(emit)
      const ready = rank ? Math.max(-1, ...t.deps.map(i => rank[i]!)) + 1 : 0
      const line = `const t${t.id}=${ready > 0 ? `d>=${ready}?${t.code}:0` : t.code};`
      chars += line.length
      if (chars > 65_536) throw new Unsupported('large transition screen')
      lines.push(line)
    }
    values.forEach(emit)
    // Only closed AST operators, validated numerical literals and slot indices;
    // callback replay, never this generated transition, authorizes a CTI.
    // oxlint-disable-next-line typescript/no-implied-eval
    return new Function('v', 'd', `${lines.join('')}return [${values.map(t => this.ref(t)).join(',')}];`) as (v: number[], depth?: number) => number[]
  }
  // Upper truth bound, not a two-valued evaluation of an incomplete state.
  // true includes UNKNOWN; false rules out this polarity for every completion.
  // In particular, polarity=false cannot prune on an unassigned atom.
  compile(p: Pred, order?: number[], polarity = true, readyAt?: number[]): (v: number[], depth: number) => boolean {
    checkWall('tiny generate screen')
    // Keep native compilation and hot execution in bounded clauses rather
    // than one giant predicate. Partial-assignment polarity is unchanged.
    if (typeof p === 'boolean') return () => p === polarity
    if (p.op === 'not') return this.compile(p.x, order, !polarity, readyAt)
    if (p.op === 'and' || p.op === 'or') {
      if (!p.xs.length) return () => (p.op === 'and') === polarity
      if (p.xs.length === 1) return this.compile(p.xs[0]!, order, polarity, readyAt)
      // Share the expression DAG inside one bounded native clause. Split only
      // when the existing code-size cap demands it, not once per atomic test.
      try { return this.compileNative(p, order, polarity, readyAt) } catch (e) {
        if (!(e instanceof Unsupported) || e.message !== 'large generated screen') throw e
      }
      const middle = Math.ceil(p.xs.length / 2), all = (p.op === 'and') === polarity
      const tests = [this.compile({op: p.op, xs: p.xs.slice(0, middle)}, order, polarity, readyAt),
        this.compile({op: p.op, xs: p.xs.slice(middle)}, order, polarity, readyAt)]
      return (v, depth) => {
        for (const test of tests) {
          checkWall('tiny predicate clause')
          if (test(v, depth) !== all) return !all
        }
        return all
      }
    }
    return this.compileNative(p, order, polarity, readyAt)
  }
  compileNative(p: Pred, order?: number[], polarity = true, readyAt?: number[]): (v: number[], depth: number) => boolean {
    checkWall('tiny native clause')
    const rank = readyAt ? readyAt.map(depth => depth - 1) : order ? this.slots.map((_, i) => order.indexOf(i)) : undefined, used: Term[] = []
    // An atomic predicate is unknown until ALL of its dependencies are set.
    // Its old per-term placeholders could not affect that result, so return
    // before evaluating the closed expression DAG instead. Once ready, every
    // dependency of every prerequisite term is ready too.
    const atomic = typeof p !== 'boolean' && p.op === 'atom'
    const ready = rank && atomic ? Math.max(-1, ...depsOf(p).map(i => rank[i]!)) + 1 : 0
    const guard = ready > 0 ? `if(d<${ready})return true;` : ''
    const code = this.predicateCode(p, atomic ? undefined : rank, used, polarity), seen = new Set<number>(), lines: string[] = []
    let chars = guard.length + code.length
    if (chars > 65_536) throw new Unsupported('large generated screen')
    const emit = (t: Term): void => {
      checkWall('tiny term code')
      if (seen.has(t.id)) return
      seen.add(t.id); t.args.forEach(emit)
      const termReady = rank && !atomic ? Math.max(-1, ...t.deps.map(i => rank[i]!)) + 1 : 0
      const line = `const t${t.id}=${termReady > 0 ? `d>=${termReady}?${t.code}:0` : t.code};`
      chars += line.length
      if (chars > 65_536) throw new Unsupported('large generated screen')
      lines.push(line)
    }
    used.forEach(emit)
    // Closed AST operators, validated numerical literals and slot indices only;
    // no identifier or external function source is interpolated. This is an
    // UNTRUSTED screen: the callback must independently replay every proposal.
    // oxlint-disable-next-line typescript/no-implied-eval
    return new Function('v', 'd', `${guard}${lines.join('')}return ${code};`) as (v: number[], d: number) => boolean
  }
}
const uniqueTerms = (ts: Term[]) => [...new Map(ts.map(t => [t.id, t])).values()]
function bindings(names: string[], domain: number[], env: Env): Env[] {
  checkWall('tiny bindings')
  if (!names.length) return [env]
  if (names.length > 5) throw new Unsupported('many binders')
  return domain.flatMap(k => bindings(names.slice(1), domain, {...env, [names[0]!]: k}))
}
// Structurally recover row addressing from COUNT BODIES, not names: one
// counted member plus a scaled row variable (or a native tuple of the two).
function gridKeys(m: Machine, size: number): Record<string, number[]> {
  const cells: Record<string, number[]> = {}
  for (const [name] of Object.entries(m.maps ?? {})) cells[name] = Array.from({length: size}, (_, i) => i)
  for (const d of Object.values(m.counts ?? {})) walk(d.body, o => {
    checkWall('tiny grid inference')
    if (o.op !== 'get' || !Object.hasOwn(cells, String(o.map))) return
    const key = o.key as E
    if (key.op === 'add') {
      const [a, b] = key.a.op === 'mul' ? [key.a, key.b] : [key.b, key.a]
      if (a.op === 'mul' && a.a.op === 'var' && b.op === 'var' && b.name === d.key && a.a.name !== d.key && a.k >= 1 && Number.isSafeInteger(a.k) && Number.isSafeInteger(a.k * size)) cells[String(o.map)] = unique([...(cells[String(o.map)] ?? []), ...Array.from({length: size * size}, (_, i) => Math.floor(i / size) * a.k + i % size)])
    }
    if (key.op === 'tup' && key.a.op === 'var' && key.b.op === 'var' && (key.a.name === d.key || key.b.name === d.key)) cells[String(o.map)] = unique([...(cells[String(o.map)] ?? []), ...Array.from({length: size * size}, (_, i) => cpair(Math.floor(i / size), i % size))])
  })
  return cells
}
/** A deliberately small heuristic scope: binary source scalars/cells by default,
 * count-bound-sized rows and Boolean carried sets. Unsupported syntax is
 * unknown. completed means this recorded finite SCREEN traversal finished;
 * exhausted additionally means it emitted no proposals. Neither establishes
 * validity, reachability, or a complete universal cover.
 * Callback false rejects a proposal and resumes that search; void/true stops
 * that target at its first proposal. Neither outcome authorizes a drop.
 * WallExpired is caught to return partial statistics; an expired parent wall
 * remains expired, and consumers must immediately check their own checkWall.
 */
export function tinyFiniteCandidates(source: Machine, m: Machine, family: Law[], params: Env,
  onCandidate: (pre: State, request: Request, violated: Law[]) => boolean | void, options: TinyFiniteOptions = {}): TinyFiniteStatistics {
  const stateValues = unique([...(options.valueDomain ?? [0, 1])]).sort((a, b) => a - b)
  const start = performance.now(), scope: TinyFiniteStatistics['scope'] = {params: {...params}, scalarValues: [...stateValues], cellValues: [...stateValues], cells: {}, inputValues: {}, inputCells: {}, binderValues: [], postTargetPruning: options.postTargetPruning === true}
  const stats: TinyFiniteStatistics = {scope, completed: false, exhausted: false, timedOut: false, unsupported: [], nodes: 0, states: 0, steps: 0, scenarios: 0, candidates: 0, postStatePrunes: 0, postRequestPrunes: 0, ms: 0}
  const unknown = (e: unknown) => { const reason = e instanceof Error ? e.message : String(e); if (!stats.unsupported.includes(reason)) stats.unsupported.push(reason) }
  try {
    checkWall('tiny start')
    if (!stateValues.length || stateValues.length > 4 || stateValues.some(n => !Number.isSafeInteger(n) || n < 0)) throw new Unsupported('invalid finite value domain')
    if (source.history || source.leasts || source.sums) throw new Unsupported('history/least/sums')
    if (!source.params.every(p => Number.isSafeInteger(params[p]) && params[p]! >= 0)) throw new Unsupported('missing/non-natural params')
    // The finite dimension comes from a parameter-only count bound. No
    // parameter name is significant. Ambiguous bounds use the largest one.
    const bounds = Object.values(m.counts ?? {}).flatMap(d => d.below.op === 'var' && Object.hasOwn(params, d.below.name) ? [params[d.below.name]!] : d.below.op === 'const' ? [d.below.value] : [])
    const size = Math.max(0, ...bounds)
    if (size < 1 || size > 4) throw new Unsupported('count grid bound outside 1..4')
    scope.cells = gridKeys(m, size)
    scope.binderValues = Array.from({length: size}, (_, i) => i)
    const slots: Slot[] = Object.keys(source.state).map(name => ({name, values: stateValues}))
    for (const name of Object.keys(source.maps ?? {})) for (const key of scope.cells[name] ?? []) { checkWall('tiny state coordinates'); slots.push({name, key, values: stateValues}) }
    const stateSlots = slots.length
    for (const name of source.inputs) {
      checkWall('tiny request domains')
      // Explicit conjunctive natural bounds are domain hints; other inputs use
      // 0..size. No domain or quotient is a trusted pruning justification.
      let hi = 16, bounded = false
      for (const c of conjuncts(source.assume ?? {op: 'and', xs: []})) {
        checkWall('tiny numeric bounds')
        if ((c.op === '<' || c.op === '<=') && c.a.op === 'var' && c.a.name === name) {
          const b = c.b.op === 'const' ? c.b.value : c.b.op === 'var' ? params[c.b.name] : undefined
          if (b !== undefined) { hi = Math.min(hi, b - Number(c.op === '<')); bounded = true }
        }
      }
      if (!bounded) hi = size
      if (!Number.isSafeInteger(hi) || hi < 0 || hi > 16) throw new Unsupported('request domain')
      const values = Array.from({length: hi + 1}, (_, i) => i)
      scope.inputValues[name] = values; slots.push({name, request: true, values})
    }
    for (const name of source.inputMaps ?? []) {
      checkWall('tiny carried coordinates')
      scope.inputCells[name] = Array.from({length: size}, (_, i) => i)
      for (const key of scope.inputCells[name]!) slots.push({name, key, request: true, values: [0, 1]})
    }
    if (slots.length > 64) throw new Unsupported('more than 64 tiny coordinates')
    const compiler = new Compiler(source, m, params, slots, scope.cells, scope.binderValues)
    const pres: Pred[] = []
    if (source.pre) pres.push(compiler.condition(source.pre, params))
    const instances = new Map<Law, Env[]>()
    for (const law of family) {
      checkWall('tiny family compile')
      if (law.some?.length) { unknown(new Unsupported('existential law')); continue }
      if ([law.forall, ...law.keys ?? []].some(k => k !== undefined && (k in source.state || source.params.includes(k) || source.inputs.includes(k)))) { unknown(new Unsupported('shadowing law binder')); continue }
      try {
        const ats = bindings(uniqueNames([law.forall, ...law.keys ?? []]), scope.binderValues, params)
        const ps = ats.map(at => compiler.condition(law.holds, at))
        pres.push(...ps); instances.set(law, ats)
      } catch (e) { if (e instanceof WallExpired) throw e; unknown(e) }
    }
    const pre = conjunction(pres)
    if (pre === false) { stats.completed = stats.exhausted = stats.unsupported.length === 0; return stats }
    // An input compared with several constants is a structural dispatch
    // coordinate. Closing it before compilation folds inactive branches and
    // quotients request coordinates irrelevant to that operation slice.
    const dispatches = new Map<string, Set<number>>()
    walk(source.step, o => {
      checkWall('tiny dispatch inference')
      if (o.op !== '=') return
      const a = o.a as E, b = o.b as E
      const [v, k] = a.op === 'var' ? [a, b] : [b, a]
      if (v.op === 'var' && k.op === 'const' && source.inputs.includes(v.name)) {
        const set = dispatches.get(v.name) ?? new Set<number>(); set.add(k.value); dispatches.set(v.name, set)
      }
    })
    const dispatch = [...dispatches].filter(([, ks]) => ks.size > 1).sort((a, b) => b[1].size - a[1].size)[0]?.[0]
    const slices = dispatch ? scope.inputValues[dispatch]!.map(value => ({...params, [dispatch]: value})) : [params]
    const emitted = new Set<Law>(), highs = slots.map(s => Math.max(...s.values))
    const writeFlags = new Set<string>()
    walk([source.step.state, source.step.maps], o => { checkWall('tiny write flags'); if (o.op === 'flag') writeFlags.add(o.name as string) })
    const slotValue = (c: Compiler, i: number, env: Env, post: boolean): Term => {
      const s = slots[i]!
      return s.key === undefined ? c.expression({op:'var',name:s.name},env,post) : c.read(s.name,s.key,env,post,[])
    }
    // Guard pruning is used only after a structural, finite-screen identity
    // check with every write-referenced flag false. This is NOT trusted by Main.
    let inactiveIdentity = false
    try {
      const off = new Compiler(source,m,params,slots,scope.cells,scope.binderValues)
      off.flagConstants = new Map([...writeFlags].map(name=>[name,false]))
      inactiveIdentity = slots.slice(0,stateSlots).every((_,i)=>slotValue(off,i,params,true).id===off.slot(i).id)
    } catch(e) { if(e instanceof WallExpired) throw e; if(!(e instanceof Unsupported)) throw e }
    const flatPreds = (p: Pred): Pred[] => typeof p !== 'boolean' && p.op === 'and' ? p.xs.flatMap(flatPreds) : [p]
    const operations: {fixed: Env, order: number[], gate: (v:number[],d:number)=>boolean, step:(v:number[])=>number[], outputs: Term[], mayFail?: (v:number[],d:number)=>boolean}[] = []
    for(const fixed of slices){
      checkWall('tiny operation compile')
      try {
        const outputs = slots.slice(0,stateSlots).map((_,i)=>slotValue(compiler,i,fixed,true))
        if(outputs.every((t,i)=>t.id===compiler.slot(i).id)) continue
        const active = inactiveIdentity && writeFlags.size ? disjunction([...writeFlags].map(name=>compiler.condition({op:'flag',name},fixed))) : true
        const enabled = conjunction([source.assume ? compiler.condition(source.assume,fixed) : true,active])
        if(enabled===false) continue
        const relevant = new Set([...depsOf(enabled),...outputs.flatMap(t=>t.deps)])
        const clauses = flatPreds(enabled).map(depsOf)
        const degrees = slots.map((_,i)=>clauses.reduce((sum,ds)=>sum+(ds.includes(i)?1/Math.max(1,ds.length):0),0))
        const order = slots.map((_,i)=>i).filter(i=>i>=stateSlots&&relevant.has(i)).sort((a,b)=>degrees[b]!-degrees[a]!||a-b)
        operations.push({fixed,order,gate:compiler.compile(enabled,order),step:compiler.compileValues(outputs),outputs})
        outputs.forEach((t,i)=>{checkWall('tiny post ranges'); highs[i]=Math.max(highs[i]!,t.hi)})
        stats.scenarios++
      } catch(e) { if(e instanceof WallExpired) throw e; unknown(e) }
    }
    const postSlots = slots.map((s,i)=>i<stateSlots?{...s,values:unique([...s.values,highs[i]!])}:s)
    const postCompiler = new Compiler(source,m,params,postSlots,scope.cells,scope.binderValues)
    const targets: Law[] = [], predicates: Pred[] = []
    for(const [law,ats] of instances){
      checkWall('tiny shared post predicates')
      try {
        const p = conjunction(ats.map(at=>postCompiler.condition(law.holds,at)))
        if(p===true) continue
        targets.push(law); predicates.push(p)
      } catch(e) { if(e instanceof WallExpired) throw e; unknown(e) }
    }
    if(!operations.length||!targets.length){stats.completed=stats.exhausted=stats.unsupported.length===0;return stats}
    const postTests = predicates.map(p => postCompiler.compile(p)), preDeps = pres.map(depsOf)
    const degrees = slots.map((_,i)=>preDeps.reduce((sum,ds)=>sum+(ds.includes(i)?1/Math.max(1,ds.length):0),0))
    const stateOrder = slots.slice(0,stateSlots).map((_,i)=>i).sort((a,b)=>degrees[b]!-degrees[a]!||a-b)
    const preTest = compiler.compile(pre,stateOrder), v = slots.map(s=>s.values[0]!)
    if (options.postTargetPruning) for (const op of operations) {
      checkWall('tiny post-target circuit')
      try {
        const order = [...stateOrder, ...op.order], rank = slots.map((_, i) => order.indexOf(i))
        // A post coordinate is unknown until every source dependency of its
        // output is assigned. Distinct outputs need not become ready together.
        const readyAt = slots.map((_, i) => i < stateSlots ? Math.max(-1, ...op.outputs[i]!.deps.map(j => rank[j]!)) + 1 : rank[i]! + 1)
        const changed = new Set(op.outputs.flatMap((t, i) => t.id === compiler.slot(i).id ? [] : [i]))
        const needed = new Set<number>(), screens: {law: Law, mayFail: (v: number[], d: number) => boolean}[] = []
        for (const [i, law] of targets.entries()) {
          checkWall('tiny post-target predicate')
          const p = predicates[i]!, deps = depsOf(p)
          // Unchanged primitive dependencies preserve this full-family law.
          if (!deps.some(j => changed.has(j))) continue
          deps.forEach(j => needed.add(j))
          try { screens.push({law, mayFail: postCompiler.compile(p, undefined, false, readyAt)}) }
          catch (e) {
            if (e instanceof WallExpired) throw e
            if (!(e instanceof Unsupported)) throw e
            unknown(e); screens.push({law, mayFail: () => true})
          }
        }
        // Share one let-bound output DAG instead of distributing each source
        // conditional through every target. Placeholder zeroes are never read
        // by a known atom until its readyAt depth has been reached.
        const partial = compiler.compileValues(op.outputs.map((t, i) => needed.has(i) ? t : compiler.constant(0)), order)
        op.mayFail = (values, depth) => {
          if (!screens.some(screen => !emitted.has(screen.law))) return false
          const post = partial(values, depth)
          for (let i = stateSlots; i < slots.length; i++) {
            const slot = slots[i]!
            post[i] = slot.key === undefined && Object.hasOwn(op.fixed, slot.name) ? op.fixed[slot.name]! : rank[i]! < 0 ? slot.values[0]! : values[i]!
          }
          return screens.some(screen => !emitted.has(screen.law) && screen.mayFail(post, depth))
        }
      } catch (e) {
        if (e instanceof WallExpired) throw e
        if (!(e instanceof Unsupported)) throw e
        unknown(e); op.mayFail = () => true
      }
    }
    const propose = (fixed:Env, violated:Law[]):void=>{
      const preState: State = {scalars:{},maps:Object.fromEntries(Object.keys(source.maps??{}).map(name=>[name,new Map<number,number>()]))}
      const request: Request = Object.fromEntries((source.inputMaps??[]).map(name=>[name,new Map<number,number>()]))
      for(let i=0;i<slots.length;i++){
        checkWall('tiny candidate materialization')
        const s=slots[i]!, value=s.request&&s.key===undefined&&Object.hasOwn(fixed,s.name)?fixed[s.name]!:v[i]!
        if(s.request){if(s.key===undefined)request[s.name]=value;else(request[s.name] as Map<number,number>).set(s.key,value)}
        else if(s.key===undefined)preState.scalars[s.name]=value
        else preState.maps[s.name]!.set(s.key,value)
      }
      const accepted=onCandidate(preState,request,violated);stats.candidates++
      if(accepted!==false)for(const law of violated){checkWall('tiny proposed targets');emitted.add(law)}
    }
    const visit = ():void=>{
      stats.states++;checkWall('tiny lawful state')
      for(const op of operations){
        checkWall('tiny operation slice')
        for(let i=stateSlots;i<slots.length;i++)v[i]=slots[i]!.values[0]!
        for(const name of source.inputs)if(Object.hasOwn(op.fixed,name))v[slots.findIndex(s=>s.request&&s.key===undefined&&s.name===name)]=op.fixed[name]!
        const requests = (d:number):void=>{
          stats.nodes++;checkWall('tiny request assignment')
          if(!op.gate(v,d))return
          if (op.mayFail && !op.mayFail(v, stateOrder.length + d)) { stats.postRequestPrunes++; return }
          if(d<op.order.length){
            const i=op.order[d]!
            for(const value of slots[i]!.values){checkWall('tiny request values');v[i]=value;requests(d+1)}
            return
          }
          const values=op.step(v)
          if(values.every((value,i)=>value===v[i]))return
          stats.steps++
          const post=v.slice();for(let i=0;i<stateSlots;i++)post[i]=values[i]!
          const violated=targets.filter((law,i)=>!emitted.has(law)&&!postTests[i]!(post,0))
          if(violated.length)propose(op.fixed,violated)
        }
        requests(0)
      }
    }
    const states = (d:number):void=>{
      stats.nodes++;checkWall('tiny state assignment')
      if(!preTest(v,d))return
      if (options.postTargetPruning && operations.every(op => !op.mayFail!(v, d))) { stats.postStatePrunes++; return }
      if(d===stateOrder.length){visit();return}
      const i=stateOrder[d]!
      // Ones first reaches enabled guards early; both values remain enumerated.
      for(const value of [...slots[i]!.values].reverse()){checkWall('tiny state values');v[i]=value;states(d+1)}
    }
    states(0)
    // completed records traversal even when proposals were emitted; exhausted
    // additionally records a proposal-free screen, never semantic validity.
    stats.completed = stats.unsupported.length === 0
    stats.exhausted = stats.completed && stats.candidates === 0
  } catch (e) { if (e instanceof WallExpired) stats.timedOut = true; else if (e instanceof Unsupported) unknown(e); else throw e }
  finally { stats.ms = performance.now() - start }
  return stats
}
const uniqueNames = (xs: (string | undefined)[]): string[] => [...new Set(xs.filter((x): x is string => x !== undefined))]
