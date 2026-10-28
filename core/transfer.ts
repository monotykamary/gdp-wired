// A datatype law said another way, proven that way, and the law read back from it (core/data.ts's proveData calls this
// where the law alone at one unfolding isn't proven). Untrusted, as the search is: each step is a node of the one
// cyclic proof kernel/cyclic.ts checks, and Lean's twin reads it as any other.
//   - Unfolding: a call to a function that isn't recursive is its body at the call's arguments, in the law and in the
//     copies below (each again, down to the recursive functions), so the induction is chosen on what the law means. A
//     law that grows past eight times its size so (definitions unfolded into each other's arguments) isn't unfolded.
//   - Bridges: a recursive function of one or two naturals that computes a built-in (+, ∸, min, max, ≤, <, =, ≥, >, ≠,
//     x + 1, x ∸ 1, 2·x, x = 0) at every argument up to 6 (12 for one) is a candidate, as is a recursive Bool function of
//     two values of one datatype that is their equality or its negation at 160 pairs of random values (half of them a
//     value and itself: a Horn system's `diseq` predicates, compare/chc-adt), unless its bridge law (the function is the
//     built-in, at every argument) is the law itself; the bridge law is proven by the search first, and only a bridge
//     proven is used.
//   - Copies: a recursive function that calls a bridged one, one unfolded, or a copied one is copied with the built-in,
//     the body or the copy in its place, and its copy law (it is its copy at every argument) proven: one node made from
//     the two bodies walked together (its recursive calls by the node's own induction, at its recursion's uses), or,
//     where the kernel refuses that, by the search with the bridges and its callees' copy laws as lemmas.
//   - The law through them: the law unfolded, its bridged calls the built-ins, its other calls the copies, proven by
//     the search (lemmas and all; through the bridges and unfolded, half the time left, then through the unfolding
//     alone); then one node, the law as stated, using that proof's node, each bridge and copy law at the calls of the
//     law (read at their arguments), each unfolded definition's fact at its call, and the congruences between a call
//     and the same call at the arguments said another way. Its goal is equalities; nothing is assumed.
// The bridges and the copies' laws are nodes like any lemma's, at levels below the law's.
import {type C, type E, n as k, walk} from './machine.ts'
import {type DataLaw, type DataVerdict, type Fn, type Options, type Program, type Proven, type SearchCtx, type Sort, type Value, type X, type Y, Bool, Integer, Nat, Val, argsOf, bindName, define, encX, encY, evalX, factsOf, fnNamed, programOf, randomValue, rankWidth, rng, schemesOf, searchIn} from './data.ts'
import {type NodeSpec, proveCyclic} from './cyclic.ts'
import {clock, pairedKeys, withDeadline} from '../kernel/prove.ts'
import {substE} from '../kernel/kernel.ts'

// --- the built-ins a function may compute ------------------------------------------------------------------------------

type Op = {name: string, args: number, ret: 'nat' | 'bool', x: (as: X[]) => X, at: (ns: number[]) => number}
const nat = (value: number): X => ({op: 'nat', value})
const cond = (c: Y): X => ({op: 'bool', c})
const OPS: Op[] = [
  {name: '+', args: 2, ret: 'nat', x: ([a, b]) => ({op: 'add', a: a!, b: b!}), at: ([a, b]) => a! + b!},
  {name: '∸', args: 2, ret: 'nat', x: ([a, b]) => ({op: 'sub', a: a!, b: b!}), at: ([a, b]) => Math.max(0, a! - b!)},
  {name: 'min', args: 2, ret: 'nat', x: ([a, b]) => ({op: 'min', a: a!, b: b!}), at: ([a, b]) => Math.min(a!, b!)},
  {name: 'max', args: 2, ret: 'nat', x: ([a, b]) => ({op: 'max', a: a!, b: b!}), at: ([a, b]) => Math.max(a!, b!)},
  {name: '≤', args: 2, ret: 'bool', x: ([a, b]) => cond({op: '<=', a: a!, b: b!}), at: ([a, b]) => +(a! <= b!)},
  {name: '<', args: 2, ret: 'bool', x: ([a, b]) => cond({op: '<', a: a!, b: b!}), at: ([a, b]) => +(a! < b!)},
  {name: '=', args: 2, ret: 'bool', x: ([a, b]) => cond({op: '=', a: a!, b: b!}), at: ([a, b]) => +(a! === b!)},
  {name: '≥', args: 2, ret: 'bool', x: ([a, b]) => cond({op: '<=', a: b!, b: a!}), at: ([a, b]) => +(a! >= b!)},
  {name: '>', args: 2, ret: 'bool', x: ([a, b]) => cond({op: '<', a: b!, b: a!}), at: ([a, b]) => +(a! > b!)},
  {name: '≠', args: 2, ret: 'bool', x: ([a, b]) => cond({op: 'not', x: {op: '=', a: a!, b: b!}}), at: ([a, b]) => +(a! !== b!)},
  {name: 'x + 1', args: 1, ret: 'nat', x: ([a]) => ({op: 'add', a: a!, b: nat(1)}), at: ([a]) => a! + 1},
  {name: 'x ∸ 1', args: 1, ret: 'nat', x: ([a]) => ({op: 'sub', a: a!, b: nat(1)}), at: ([a]) => Math.max(0, a! - 1)},
  {name: '2·x', args: 1, ret: 'nat', x: ([a]) => ({op: 'mul', k: 2, a: a!}), at: ([a]) => 2 * a!},
  {name: 'x = 0', args: 1, ret: 'bool', x: ([a]) => cond({op: '=', a: a!, b: nat(0)}), at: ([a]) => +(a! === 0)},
]
// A sum Σ cᵢ·xᵢ + c₀ of naturals (cᵢ, c₀ ≥ 0): the built-in of a function of three or four naturals (add3, add3acc), or
// of one or two that none of OPS is.
const linear = (cs: number[], c0: number): Op => {
  const names = ['x', 'y', 'z', 'w'], name = [...cs.flatMap((c, i) => (c ? [`${c === 1 ? '' : `${c}·`}${names[i]}`] : [])), ...(c0 || cs.every(c => !c) ? [String(c0)] : [])].join(' + ')
  const term = (a: X, c: number): X => (c === 1 ? a : {op: 'mul', k: c, a})
  return {name, args: cs.length, ret: 'nat', at: ns => cs.reduce((t, c, i) => t + c * ns[i]!, c0),
    x: as => { const parts = [...cs.flatMap((c, i) => (c ? [term(as[i]!, c)] : [])), ...(c0 || cs.every(c => !c) ? [nat(c0)] : [])]; return parts.slice(1).reduce<X>((t, x) => ({op: 'add', a: t, b: x}), parts[0]!) }}
}
const fnOf = (name: string): Fn => { const f = fnNamed(name); if (!f) throw new Error(`no function ${name}`); return f }
const recursive = (f: Fn) => f.decreases !== undefined
// Recursive at all (structural, or well-founded): never unfolded at a call.
const taken = (f: Fn) => recursive(f) || f.measure !== undefined
// The built-in a recursive function of naturals (structural, or well-founded: its termination proven) computes at every
// argument up to 6 (one argument: up to 12; three: up to 5; four: up to 3), if one.
function builtinOf(f: Fn): Op | undefined {
  if (taken(f) && !f.paramFns.length && f.ret === 'bool' && f.params.length === 2 && typeof f.params[0]!.sort === 'object' && f.params[0]!.sort === f.params[1]!.sort && !f.params[0]!.sort.abstract) return equalityOf(f)
  if (!taken(f) || f.paramFns.length || !(f.ret === 'nat' || f.ret === 'bool') || !f.params.every(q => q.sort === 'nat')) return undefined
  const n = f.params.length
  if (n < 1 || n > 4) return undefined
  const top = [12, 6, 5, 3][n - 1]!, points: number[][] = [[]]
  for (let i = 0; i < n; i++) points.splice(0, points.length, ...points.flatMap(p => Array.from({length: top + 1}, (_, a) => [...p, a])))
  const values = new Map<string, number>()
  const at = (ns: number[]): number | undefined => {
    const key = ns.join(',')
    if (!values.has(key)) { try { values.set(key, evalX({op: 'call', fn: f.name, args: ns.map(nat)}, new Map(), {}) as number) } catch { return undefined } }
    return values.get(key)
  }
  const agrees = (op: Op) => points.every(ns => at(ns) === op.at(ns))
  const named = OPS.find(op => op.args === n && op.ret === f.ret && agrees(op))
  if (named || f.ret !== 'nat') return named
  // (its value at zero and at each unit point, then checked at every point)
  const c0 = at(Array(n).fill(0)), cs = Array.from({length: n}, (_, i) => { const e = Array(n).fill(0); e[i] = 1; const v = at(e); return v === undefined || c0 === undefined ? -1 : v - c0 })
  if (c0 === undefined || cs.some(c => c < 0)) return undefined
  const op = linear(cs, c0)
  return agrees(op) ? op : undefined
}
// = or ≠, if f (a Bool function of two values of one datatype) is it at 160 pairs of random values, half of them a value
// and itself.
function equalityOf(f: Fn): Op | undefined {
  const rand = rng(3), s = f.params[0]!.sort, args: X[] = [{op: 'var', name: '$p'}, {op: 'var', name: '$q'}]
  let eq = true, ne = true
  for (let i = 0; i < 160 && (eq || ne); i++) {
    const a = randomValue(s, rand, 1 + (i % 6)), b = i % 2 ? a : randomValue(s, rand, 1 + (i % 6)), same = JSON.stringify(a) === JSON.stringify(b)
    let v: Value
    try { v = evalX({op: 'call', fn: f.name, args}, new Map([['$p', a], ['$q', b]]), {}) } catch { return undefined }
    eq &&= v === +same; ne &&= v === +!same
  }
  return eq ? OPS.find(o => o.name === '=') : ne ? OPS.find(o => o.name === '≠') : undefined
}
// Whether `y` is f's bridge law: f at distinct variables equal (either side) to the built-in at them.
function isBridge(y: Y, f: Fn, op: Op): boolean {
  if (y.op !== '=') return false
  const sides: [X, X][] = [[y.a, y.b], [y.b, y.a]]
  return sides.some(([c, x]) => c.op === 'call' && c.fn === f.name && c.args.every(a => a.op === 'var') && new Set(c.args.map(a => JSON.stringify(a))).size === c.args.length
    && JSON.stringify(x) === JSON.stringify(op.x(c.args)))
}
const callsOf = (t: unknown): string[] => { const out: string[] = []; walk(t, o => { if (o.op === 'call') out.push(o.fn as string) }); return out }

// What a law may go through: the bridges' candidates (by their values), and the functions it reaches that aren't
// recursive (unfolded). None of either: the law as stated. A candidate whose bridge law is the law itself isn't one:
// its search would be the law's own, done again on the law after it (core/data.test.ts's nearPlus: 114,197 units of
// work for the bridge, then 35,367 for the law, `runs/datafix/trace0`).
export type Plan = {bridges: Map<string, Op>, unfolds: boolean}
export function transferPlan(l: DataLaw): Plan | undefined {
  const p = programOf([l]), bridges = new Map<string, Op>()
  for (const f of p.fns) { const op = builtinOf(f); if (op && !isBridge(l.holds, f, op)) bridges.set(f.name, op) }
  const unfolds = p.fns.some(f => !taken(f))
  return bridges.size || unfolds ? {bridges, unfolds} : undefined
}

// --- the law said another way ------------------------------------------------------------------------------------------

// A function's body at arguments (its parameters replaced, each bound name fresh).
function instantiate(f: Fn, args: X[]): X {
  const sub = new Map(f.params.map((q, i) => [`${f.name}.${q.name}`, args[i]!])), ren = new Map<string, string>()
  const fresh = (b: string) => { const n = bindName(b.replace(/#\d+$/, '')); ren.set(b, n); return n }
  const go = (t: unknown): unknown => {
    if (Array.isArray(t)) return t.map(go)
    if (!t || typeof t !== 'object') return t
    const o = t as Record<string, unknown>
    if (o.op === 'var') { const name = o.name as string; return sub.get(name) ?? (ren.has(name) ? {op: 'var', name: ren.get(name)} : o) }
    if (o.op === 'match') { const cases = (o.cases as {binds: string[], body: X}[]).map(c => ({binds: c.binds.map(fresh), body: c.body})); return {...o, of: go(o.of), cases: cases.map(c => ({binds: c.binds, body: go(c.body)}))} }
    if (o.op === 'natmatch') { const pred = fresh(o.pred as string); return {...o, of: go(o.of), zero: go(o.zero), pred, succ: go(o.succ)} }
    return Object.fromEntries(Object.entries(o).map(([key, v]) => [key, go(v)]))
  }
  return go(f.body()) as X
}
// A term with each bridged call the built-in and each call to a copied function its copy's; in a law (`unfold`), a call
// to a function that isn't recursive also its body. `holds` of a condition made a value is the condition.
function rewriter(bridges: Map<string, Op>, copies: Map<string, string>, unfold: boolean, ren = new Map<string, string>()) {
  let unfolded = 0
  const rx = (x: X): X => {
    switch (x.op) {
      case 'var': return ren.has(x.name) ? {op: 'var', name: ren.get(x.name)!} : x
      case 'nat': return x
      case 'add': case 'sub': case 'min': case 'max': return {op: x.op, a: rx(x.a), b: rx(x.b)}
      case 'mul': return {op: 'mul', k: x.k, a: rx(x.a)}
      case 'prod': case 'iadd': case 'isub': return {op: x.op, a: rx(x.a), b: rx(x.b)}
      case 'mod': case 'div': case 'imod': case 'idiv': case 'imul': return {op: x.op, k: x.k, a: rx(x.a)}
      case 'ineg': case 'ofnat': return {op: x.op, a: rx(x.a)}
      case 'int': return x
      case 'if': return {op: 'if', c: ry(x.c), then: rx(x.then), else: rx(x.else)}
      case 'bool': return {op: 'bool', c: ry(x.c)}
      case 'apply': return {op: 'apply', param: x.param, arg: rx(x.arg)}
      case 'size': return {op: 'size', data: x.data, of: rx(x.of)}
      case 'ctor': return {...x, args: x.args.map(rx)}
      case 'match': return {...x, of: rx(x.of), cases: x.cases.map(c => ({binds: c.binds, body: rx(c.body)}))}
      case 'natmatch': return {...x, of: rx(x.of), zero: rx(x.zero), succ: rx(x.succ)}
      case 'call': {
        const op = bridges.get(x.fn)
        if (op) return op.x(x.args.map(rx))
        if (unfold && !taken(fnOf(x.fn))) { if (++unfolded > 400) throw new RangeError('unfolded past 400 calls'); return rx(instantiate(fnOf(x.fn), x.args)) }
        return {op: 'call', fn: copies.get(x.fn) ?? x.fn, args: x.args.map(rx)}
      }
    }
  }
  const ry = (y: Y): Y => {
    switch (y.op) {
      case '<': case '<=': case '=': case 'i<': case 'i<=': return {op: y.op, a: rx(y.a), b: rx(y.b)}
      case 'and': case 'or': return {op: y.op, xs: y.xs.map(ry)}
      case 'not': return {op: 'not', x: ry(y.x)}
      case 'is': return {...y, of: rx(y.of)}
      case 'holds': { const x = rx(y.x); return x.op === 'bool' ? x.c : {op: 'holds', x} }
    }
  }
  return {rx, ry}
}
const valueOf = (s: Sort, x: X): Nat | Bool | Val | Integer => (s === 'nat' ? new Nat(x) : s === 'bool' ? new Bool(x.op === 'bool' ? x.c : {op: 'holds', x}) : s === 'int' ? new Integer(x) : new Val(s, x))
// The copies made, by function and bridges (a law proven again reads the same copies).
const made = new WeakMap<Fn, Map<string, string>>()
const freshName = (base: string) => { let n = base; for (let i = 2; fnNamed(n); i++) n = `${base}${i}`; return n }

type Built = {p: Program, lstar: DataLaw, bridges: {fn: Fn, op: Op, law: DataLaw}[], equivs: {fn: Fn, law: DataLaw}[], copies: Map<string, string>, unfolded: boolean}
// The law through the bridges `bridged`: the copies (made once), the law said with them, the bridge and copy laws, and
// the program of all of them; none where a copied function is in a ring of several (its copy law would be mutual).
function build(l: DataLaw, bridged: Map<string, Op>, unfold: boolean): Built | undefined {
  // Copied: a function that calls a bridged one, or (unfolding) one that isn't recursive, or a copied one; a function
  // that isn't recursive is unfolded where it is called instead.
  const p0 = programOf([l]), reach = new Set<string>(), unfolded = (n: string) => unfold && !taken(fnOf(n))
  for (let changed = true; changed;) { changed = false; for (const f of p0.fns) if (!bridged.has(f.name) && !unfolded(f.name) && !reach.has(f.name) && callsOf(f.body()).some(g => bridged.has(g) || unfolded(g) || reach.has(g))) { reach.add(f.name); changed = true } }
  if ([...reach].some(n => fnOf(n).ring.length > 1)) return undefined
  const key = `${unfold}|${[...bridged].map(([f, op]) => `${f}:${op.name}`).sort().join(',')}`, copies = new Map<string, string>()
  for (const n of reach) { const f = fnOf(n), had = made.get(f)?.get(key); if (had && fnNamed(had)) copies.set(n, had) }
  for (const n of reach) {
    if (copies.has(n)) continue
    const f = fnOf(n), name = freshName(`${n}_bi`)
    copies.set(n, name)
    if (!made.has(f)) made.set(f, new Map())
    made.get(f)!.set(key, name)
  }
  for (const n of reach) {
    const f = fnOf(n), name = copies.get(n)!
    if (fnNamed(name)) continue
    const ren = new Map(f.params.map(q => [`${f.name}.${q.name}`, `${name}.${q.name}`]))
    let body: X
    try { body = rewriter(bridged, copies, unfold, ren).rx(f.body()) } catch (e) { if (e instanceof RangeError) return undefined; throw e }
    define(name, Object.fromEntries(f.params.map(q => [q.name, q.sort])), f.ret, () => valueOf(f.ret, body))
  }
  let holds: Y
  try { holds = rewriter(bridged, copies, unfold).ry(l.holds) } catch (e) { if (e instanceof RangeError) return undefined; throw e }
  const lstar: DataLaw = {name: `${l.name}, said through ${[...bridged.keys()].length ? 'the built-ins' : 'its definitions'}`, vars: l.vars, holds, params: l.params}
  // (none the same as the law, and none past eight times its size: definitions unfolded into each other's arguments)
  const size = (y: Y) => JSON.stringify(y).length
  if (JSON.stringify(lstar.holds) === JSON.stringify(l.holds) || size(lstar.holds) > 8 * size(l.holds) + 4000) return undefined
  const v = (name: string): X => ({op: 'var', name})
  // Only the copies the law said through them reaches (each with those its copy calls).
  const p1 = programOf([lstar]), back = new Map([...copies].map(([a, b]) => [b, a]))
  const bridges = [...bridged].map(([f, op]) => {
    const fn = fnOf(f), vs = fn.params.map(q => q.name)
    return {fn, op, law: {name: `${f} is ${op.name}`, vars: fn.params.map(q => ({name: q.name, sort: q.sort})), holds: {op: '=', a: {op: 'call', fn: f, args: vs.map(v)}, b: op.x(vs.map(v))}, params: []} as DataLaw}
  })
  const equivs = p1.fns.filter(f => back.has(f.name)).map(c => {
    const fn = fnOf(back.get(c.name)!), vs = fn.params.map(q => q.name), params = [...new Set(fn.paramFns)]
    return {fn, law: {name: `${fn.name} is ${c.name}`, vars: fn.params.map(q => ({name: q.name, sort: q.sort})), holds: {op: '=', a: {op: 'call', fn: fn.name, args: vs.map(v)}, b: {op: 'call', fn: c.name, args: vs.map(v)}}, params} as DataLaw}
  })
  const p = programOf([l, lstar, ...bridges.map(b => b.law), ...equivs.map(e => e.law)])
  return {p, lstar, bridges, equivs, copies, unfolded: unfold}
}

// --- the proof ---------------------------------------------------------------------------------------------------------

const yes: C = {op: '<=', a: k(0), b: k(0)}
const top = (pr: Proven): number => Math.max(0, ...pr.nodes.map(n => (n.rank[0]?.op === 'const' ? n.rank[0].value : 0)))
const verify = (fs: ReturnType<typeof factsOf>, specs: NodeSpec[], until: number) => {
  const was = pairedKeys.skip
  pairedKeys.skip = true
  try { return withDeadline(until, () => proveCyclic(fs.facts, specs)) } finally { pairedKeys.skip = was }
}

// The law through its plan: the bridges proven (those not proven left out, and the rest built again), the copies' laws,
// the law said through them, and the node from that to the law. Undefined where any of it isn't proven.
export function proveThrough(l: DataLaw, plan: Plan, opts: Options, until: number): (DataVerdict & {tried: number}) | undefined {
  const t0 = performance.now()
  let bridged = new Map(plan.bridges), tried = 0
  for (;;) {
    if (clock() > until) return undefined
    // (unfolded where that stays within its size, else the bridges alone)
    const b = (plan.unfolds ? build(l, bridged, true) : undefined) ?? (bridged.size ? build(l, bridged, false) : undefined)
    if (!b) return undefined
    // One chain of nodes: each bridge (by the search), each copy's law (its node made, or by the search), in order.
    const fs = factsOf(b.p), chain: Proven[] = [], nodes: NodeSpec[] = [], nodeOf = new Map<string, number>()
    const add = (pr: Proven) => { chain.push(pr); nodes.splice(0, nodes.length, ...pr.nodes); nodeOf.set(pr.law.name, nodes.findIndex(n => n.name === pr.spec.name)) }
    const ctx = (): SearchCtx => ({p: b.p, fs, base: [...chain], level: chain.length ? top(chain.at(-1)!) : 0})
    const lost: string[] = []
    for (const x of b.bridges) {
      const r = searchIn(x.law, opts, Math.min(until, clock() + 6000 * (opts.patience ?? 1)), ctx())
      tried += r.verdict.tried
      if (r.out) add(r.out)
      else lost.push(x.fn.name)
    }
    if (lost.length) {
      for (const n of lost) bridged.delete(n)
      if (!bridged.size && !plan.unfolds) return undefined
      continue
    }
    for (const x of b.equivs) {
      const level = (chain.length ? top(chain.at(-1)!) : 0) + 1, made = copyNode(x, b, fs, nodeOf, nodes.length, level)
      const checked = made && verify(fs, [...nodes, made], Math.min(until, clock() + 4000))
      if (made && checked && checked.proven && checked.checked) { add({law: x.law, spec: made, nodes: [...nodes, made]}); continue }
      const r = searchIn(x.law, {...opts, lemmas: []}, Math.min(until, clock() + 8000 * (opts.patience ?? 1)), ctx())
      tried += r.verdict.tried
      if (!r.out) return undefined
      add(r.out)
    }
    // (through the bridges and unfolded: half the time left, the other half through the unfolding alone, the functions
    // as written)
    const again = b.unfolded && bridged.size > 0
    const r = searchIn(b.lstar, opts, again ? clock() + (until - clock()) / 2 : until, {p: b.p, fs, base: [], level: 0, merge: true})
    tried += r.verdict.tried
    if (!r.out && again && clock() < until) { bridged = new Map(); continue }
    if (!r.out) return {...r.verdict, proven: false, checked: false, law: l.name, counterexample: undefined, tried}
    // The nodes: the chain's, then the law's said through them, then the law's own.
    const specs: NodeSpec[] = [...nodes], names = new Set(specs.map(n => n.name)), off = specs.length
    for (const n of r.out.nodes) {
      let name = n.name
      for (let i = 2; names.has(name); i++) name = `${n.name} (${i})`
      names.add(name)
      specs.push({...n, name, uses: n.uses.map(u => ({...u, node: u.node + off}))})
    }
    const lnode = off + r.out.nodes.indexOf(r.out.spec)
    const node = lawNode(l, b, fs, nodeOf, lnode, Math.max(top(r.out), ...chain.map(top)) + 1)
    if (!node) return undefined
    specs.push(node)
    const v = verify(fs, specs, Math.max(until, clock() + 3000))
    if (!v.proven || !v.checked) return undefined
    const through = [...b.bridges.map(x => `${x.fn.name} is ${x.op.name}`), ...b.equivs.map(x => x.law.name), ...(b.unfolded ? [`unfolded: ${programOf([l]).fns.filter(f => !taken(f)).map(f => f.name).join(', ')}`] : [])]
    return {law: l.name, proven: true, checked: true, proof: v, lemmas: [...b.bridges.map(x => x.law.name), ...b.equivs.map(x => x.law.name), ...r.verdict.lemmas], scheme: `${r.verdict.scheme ?? 'no induction'}, through the law ${b.lstar.name}`, tried, program: b.p, node: specs.length - 1, ms: Math.round(performance.now() - t0), through}
  }
}

// Two terms, one of the law (or a function's body) and one said through the bridges, walked together: where they read
// different things, the reason they are equal, recorded (a bridge's or a copy's law at the call's arguments, an unfolded
// function's fact there, a congruence of a map at two keys). `own`: a function whose read is its copy's by the node's own
// induction (a copy's law: its recursive calls, given by the uses of its scheme).
function walker(b: Built, fs: ReturnType<typeof factsOf>, nodeOf: Map<string, number>, own?: string) {
  const p = b.p, insts: NodeSpec['insts'] = [], uses: NodeSpec['uses'] = [], seen = new Set<string>()
  const bridgeOf = new Map(b.bridges.map(x => [x.fn.name, x])), copyOf = new Map(b.equivs.map(x => [x.fn.name, x]))
  const id = (t: unknown) => JSON.stringify(t)
  const inst = (fact: string, at: E[]) => { const i = fs.at.get(fact); if (i === undefined) return false; const key = id([i, at]); if (!seen.has(key)) { seen.add(key); insts.push({fact: i, at}) } return true }
  const use = (law: string, subst: Record<string, E>) => { const node = nodeOf.get(law); if (node === undefined) return false; const key = id([node, subst]); if (!seen.has(key)) { seen.add(key); uses.push({node, subst, guard: yes}) } return true }
  const factBody = (f: Fn, as: E[]): E => {
    const holds = fs.facts[fs.at.get(`fn ${f.name}`)!]!.holds, eq = (holds.op === 'and' ? holds.xs[0]! : holds) as C & {op: '='}
    return substE(eq.b, {vars: Object.fromEntries(f.params.map((q, i) => [`${f.name}.${q.name}`, as[i]!])), maps: {}, flags: {}})
  }
  // A read of the law's side one step closer to the other side (the reason recorded), or undefined.
  const step = (a: E & {op: 'get'}): E | undefined => {
    const f = fnNamed(a.map), n = fs.arity.get(a.map) ?? 1, as = argsOf(a.key, n)
    if (!f || !as) return undefined
    const br = bridgeOf.get(f.name)
    if (br) {
      if (!use(br.law.name, Object.fromEntries(f.params.map((q, i) => [q.name, as[i]!])))) return undefined
      return substE(encX(p, br.op.x(as.map((_, i) => ({op: 'var', name: `a$${i}`}))), new Map()), {vars: Object.fromEntries(as.map((a, i) => [`a$${i}`, a])), maps: {}, flags: {}})
    }
    if (!taken(f) && b.unfolded) return inst(`fn ${f.name}`, as) ? factBody(f, as) : undefined
    const copy = b.copies.get(f.name)
    if (!copy) return undefined
    if (f.name === own) return {op: 'get', map: copy, key: a.key}
    const cp = copyOf.get(f.name)
    return cp && use(cp.law.name, Object.fromEntries(f.params.map((q, i) => [q.name, as[i]!]))) ? {op: 'get', map: copy, key: a.key} : undefined
  }
  const walkE = (a: E, c: E): boolean => {
    if (id(a) === id(c)) return true
    if (a.op === 'get') {
      if (c.op === 'get' && c.map === a.map) {
        const n = fs.arity.get(a.map) ?? 1, as = argsOf(a.key, n), cs = argsOf(c.key, n)
        if (!as || !cs || !as.every((x, i) => walkE(x, cs[i]!))) return false
        return inst(`cong ${a.map}`, [...as, ...cs])
      }
      const next = step(a)
      return !!next && walkE(next, c)
    }
    if (a.op !== c.op) return false
    switch (a.op) {
      case 'add': case 'sub': case 'min': case 'max': case 'prod': { const o = c as typeof a; return walkE(a.a, o.a) && walkE(a.b, o.b) }
      case 'mul': { const o = c as typeof a; return a.k === o.k && walkE(a.a, o.a) }
      case 'if': { const o = c as typeof a; return walkC(a.c, o.c) && walkE(a.then, o.then) && walkE(a.else, o.else) }
      case 'var': case 'const': return false
    }
  }
  const walkC = (a: C, c: C): boolean => {
    if (id(a) === id(c)) return true
    // A condition made a value, read as the condition (`holds`): f(..) = 1 where f's read becomes if (cond, 1, 0).
    if (a.op === '=' && a.b.op === 'const' && a.b.value === 1 && (a.a.op === 'get' || a.a.op === 'if') && !(c.op === '=' && c.a.op === a.a.op && (c.a.op !== 'get' || a.a.op !== 'get' || c.a.map === a.a.map))) {
      let x: E | undefined = a.a
      while (x && x.op === 'get' && !(c.op === '=' && c.a.op === 'get' && c.a.map === x.map)) x = step(x)
      if (x && x.op === 'if' && x.then.op === 'const' && x.then.value === 1 && x.else.op === 'const' && x.else.value === 0 && walkC(x.c, c)) return true
    }
    if (a.op !== c.op) return false
    switch (a.op) {
      case '<': case '<=': case '=': { const o = c as typeof a; return walkE(a.a, o.a) && walkE(a.b, o.b) }
      case 'and': case 'or': { const o = c as typeof a; return a.xs.length === o.xs.length && a.xs.every((x, i) => walkC(x, o.xs[i]!)) }
      case 'not': return walkC(a.x, (c as typeof a).x)
      case 'all': case 'flag': return false
    }
  }
  return {walkC, walkE, insts, uses, inst}
}

// A node's rank is (level, the measure's place, 0 or 1), the measure's place as wide as the program's widest measure
// (core/data.ts's attempt): the zeros after the `n` components given, so every node's rank has one length.
const pad = (p: Program, n: number): E[] => Array.from({length: rankWidth(p) - n}, () => k(0))
// The law's node: its conclusion, using the law said through the bridges (at its own variables) and the walk's reasons.
function lawNode(l: DataLaw, b: Built, fs: ReturnType<typeof factsOf>, nodeOf: Map<string, number>, lnode: number, level: number): NodeSpec | undefined {
  const w = walker(b, fs, nodeOf), concl = encY(b.p, l.holds, new Map())
  if (!w.walkC(concl, encY(b.p, b.lstar.holds, new Map()))) return undefined
  return {name: `${l.name} (through ${b.lstar.name})`, hyps: [], concl, rank: [k(level), ...pad(b.p, 0), k(0)], insts: w.insts, uses: [{node: lnode, subst: {}, guard: yes}, ...w.uses]}
}

// A copy's law, f(xs) = f'(xs), as one node at index `self`: both definitions' facts at xs, their bodies walked together
// (f's own recursive calls its copy's by the node itself, at the uses of f's recursion scheme), the shape of the argument
// the recursion is on (its rank, its size).
function copyNode(x: {fn: Fn, law: DataLaw}, b: Built, fs: ReturnType<typeof factsOf>, nodeOf: Map<string, number>, self: number, level: number): NodeSpec | undefined {
  const f = x.fn, copy = b.copies.get(f.name)!, vs = f.params.map(q => ({op: 'var', name: q.name}) as E)
  const w = walker(b, fs, nodeOf, f.name)
  if (!w.inst(`fn ${f.name}`, vs) || !w.inst(`fn ${copy}`, vs)) return undefined
  const body = (g: string) => { const h = fs.facts[fs.at.get(`fn ${g}`)!]!.holds, eq = (h.op === 'and' ? h.xs[0]! : h) as C & {op: '='}; return substE(eq.b, {vars: Object.fromEntries(f.params.map((q, i) => [`${g}.${q.name}`, vs[i]!])), maps: {}, flags: {}}) }
  if (!w.walkE(body(f.name), body(copy))) return undefined
  const scheme = recursive(f) ? schemesOf(b.p, x.law).find(sc => sc.name.startsWith(`recursion of ${f.name} `)) : undefined
  if (recursive(f) && !scheme) return undefined
  const on = scheme?.on, size: E = !on ? k(0) : on.d === 'nat' ? {op: 'var', name: on.v} : {op: 'get', map: `${on.d.name}.size`, key: {op: 'var', name: on.v}}
  if (on && on.d !== 'nat') w.inst(`shape ${on.d.name}`, [{op: 'var', name: on.v}])
  return {name: `${x.law.name} (its copy, made)`, hyps: [], concl: encY(b.p, x.law.holds, new Map()), rank: [k(level), size, ...pad(b.p, 1), k(0)], insts: w.insts,
    uses: [...(scheme?.uses ?? []).map(u => ({node: self, subst: u.subst, guard: u.guard})), ...w.uses]}
}
