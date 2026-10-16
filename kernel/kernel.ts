// The kernel: the only part of a machine proof that is trusted, besides check.ts. Provers (prove.ts, or anything else)
// are untrusted; they hand the kernel a proof tree and the kernel either accepts it or doesn't.
//
// A goal is a list of hypotheses over naturals (quantifier-free: +, ∸, × by a constant, min, max, if, map reads) that
// can't all hold. A proof is a tree of splits on linear atoms (lin <= 0, or lin >= 1), with a derivation at each leaf.
// At a leaf, the kernel takes the path's atoms, every linear fact the hypotheses give under the path (a comparison whose
// ifs, mins and truncations the path decides; the parts of a conjunction; the one disjunct left when the path refutes
// the others), each variable >= 0, and, for two reads of one map at keys the path proves equal, their equality; the
// leaf's derivation must refute them (check.ts). Splits are trivially exhaustive, so a tree whose leaves all check
// means the hypotheses never hold together.
//
// Machines: `obligations` turns a machine and a set of laws into goals, the induction rule spelled out: each law holds
// at the start, and one step from a state where every law in the set holds keeps it. A law that holds at every key is
// assumed at whatever keys the proof names (instantiating ∀ is sound at any term) and is proven at a fresh key. The
// whole set is checked, so nothing is assumed that isn't proven.
//
// Two kinds of assumption: `pre`, about the params alone, is a precondition (the law is claimed only for params that
// meet it), so it holds at the start and at every step; `assume`, about each request, holds only at a step, since no
// request has come at the start.
import {checkRefutation} from '../core/check.ts'
import type {C, E, Law, Machine} from '../core/machine.ts'
import {type Constraint, type Lin, type Step, add, k, scale, sub, v} from '../core/solver.ts'

// An exhaustive switch's default: TypeScript proves it unreachable, and if it is reached anyway (a value from outside
// the types), it fails loudly instead of returning undefined.
export function unreachable(value: never): never { throw new Error(`unhandled case: ${JSON.stringify(value)}`) }

export type Tree = {split: Lin, yes: Tree, no: Tree} | {leaf: Step[], products?: [number, number][]}
export type Goal = {name: string, hyps: C[]}

// The path: atoms decided so far, by their canonical text. yes: lin <= 0; no: lin >= 1.
export type Path = Map<string, {lin: Lin, holds: boolean}>
export const canon = (lin: Lin) => Object.keys(lin).sort().map(key => `${key}:${lin[key]}`).join(',')
export const atomOf = (lin: Lin, holds: boolean): Constraint => ({lin: holds ? lin : add(k(1), scale(lin, -1)), label: ''})

// Is lin <= 0 decided by the path? A constant atom decides itself.
// Over the integers lin <= 0 fails exactly when 1 - lin <= 0 holds, so either atom decides the other.
function decide(lin: Lin, path: Path): boolean | undefined {
  if (Object.keys(lin).every(key => key === '1')) return (lin['1'] ?? 0) <= 0
  const direct = path.get(canon(lin))?.holds
  if (direct !== undefined) return direct
  const flipped = path.get(canon(add(k(1), scale(lin, -1))))?.holds
  return flipped === undefined ? undefined : !flipped
}

// A term's linear form under the path, or undefined if the path leaves one of its choices open.
// Reads become cells, named by map and key: `M[key]`.
export function linear(e: E, path: Path): Lin | undefined {
  switch (e.op) {
    case 'var': return e.name === '1' || /[*[\],:]/.test(e.name) ? undefined : v(e.name) // those characters build cells and monomials
    case 'const': return k(e.value)
    case 'mul': { const a = linear(e.a, path); return a && scale(a, e.k) }
    case 'prod': { const a = linear(e.a, path), b = linear(e.b, path); return a && b && times(a, b) }
    case 'add': { const a = linear(e.a, path), b = linear(e.b, path); return a && b && add(a, b) }
    case 'sub': case 'min': case 'max': {
      const a = linear(e.a, path), b = linear(e.b, path)
      if (!a || !b) return undefined
      const aLeB = decide(sub(a, b), path), bLeA = decide(sub(b, a), path)
      if (e.op === 'sub') return bLeA === true ? sub(a, b) : bLeA === false ? k(0) : undefined
      if (aLeB === undefined) return undefined
      return (e.op === 'min') === aLeB ? a : b
    }
    case 'if': { const c = truth(e.c, path); return c === undefined ? undefined : linear(c ? e.then : e.else, path) }
    case 'get': { const key = linear(e.key, path); return key && v(`${e.map}[${canon(key)}]`) }
  }
}

// Products: multiply out, each monomial (variables joined by '*', sorted) one more natural variable. Forgetting how
// monomials relate (x*x to x, say) only weakens what a leaf may use, so it stays sound; distributing is what proves
// spend <= m·count over a node from the same law at its children. Map reads can't be factors.
function times(a: Lin, b: Lin): Lin | undefined {
  const out: Lin[] = []
  for (const [p, cp] of Object.entries(a)) for (const [q, cq] of Object.entries(b)) {
    if (p.includes('[') || q.includes('[')) return undefined
    const factors = [...(p === '1' ? [] : p.split('*')), ...(q === '1' ? [] : q.split('*'))].sort()
    out.push({[factors.length ? factors.join('*') : '1']: cp * cq})
  }
  return add(...out)
}

// The atoms (lin <= 0 each) that make a comparison true, and those that make it false (one of which holds).
function comparison(c: Extract<C, {a: E}>, path: Path): {when: Lin[], unless: Lin[][]} | undefined {
  const a = linear(c.a, path), b = linear(c.b, path)
  if (!a || !b) return undefined
  const ab = sub(a, b), ba = sub(b, a)
  if (c.op === '<=') return {when: [ab], unless: [[add(ba, k(1))]]}
  if (c.op === '<') return {when: [add(ab, k(1))], unless: [[ba]]}
  return {when: [ab, ba], unless: [[add(ab, k(1))], [add(ba, k(1))]]}
}

// Kleene truth under the path: true, false, or undefined when open.
export function truth(c: C, path: Path): boolean | undefined {
  switch (c.op) {
    case 'flag': throw new Error('flags are inlined before the kernel sees them')
    case 'not': { const t = truth(c.x, path); return t === undefined ? undefined : !t }
    case 'and': case 'or': {
      const ts = c.xs.map(y => truth(y, path)), dominant = c.op === 'or'
      return ts.includes(dominant) ? dominant : ts.every(t => t === !dominant) ? !dominant : undefined
    }
    case '<': case '<=': case '=': {
      const cmp = comparison(c, path)
      if (!cmp) return undefined
      const ts = cmp.when.map(lin => decide(lin, path))
      return ts.includes(false) ? false : ts.every(t => t === true) ? true : undefined
    }
    default: return unreachable(c)
  }
}

// The linear facts a hypothesis gives under the path (each lin <= 0).
export function facts(c: C, path: Path, positive = true): Lin[] {
  switch (c.op) {
    case 'flag': throw new Error('flags are inlined before the kernel sees them')
    case 'not': return facts(c.x, path, !positive)
    case 'and': case 'or': {
      if ((c.op === 'and') === positive) return c.xs.flatMap(y => facts(y, path, positive))
      const open = c.xs.filter(y => truth(y, path) !== !positive)
      return open.length === 0 ? [k(1)] : open.length === 1 ? facts(open[0]!, path, positive) : []
    }
    case '<': case '<=': case '=': {
      const cmp = comparison(c, path)
      if (!cmp) return []
      if (positive) return cmp.when
      const open = cmp.unless.filter(atoms => !atoms.some(lin => decide(lin, path) === false))
      return open.length === 0 ? [k(1)] : open.length === 1 ? open[0]! : []
    }
    default: return unreachable(c)
  }
}

// What a leaf's derivation must refute.
export function leafConstraints(goal: Goal, path: Path): Constraint[] {
  const rows: Constraint[] = [...path.values()].map(a => atomOf(a.lin, a.holds))
  for (const h of goal.hyps) for (const lin of facts(h, path)) rows.push({lin, label: ''})
  const names = new Set(rows.flatMap(r => Object.keys(r.lin).filter(key => key !== '1')))
  // Two reads of one map whose keys the path proves equal are equal.
  const cells = [...names].filter(name => name.includes('[')).map(name => ({name, map: name.slice(0, name.indexOf('[')), key: keyOf(name)}))
  for (const [i, p] of cells.entries()) for (const q of cells.slice(i + 1)) {
    if (p.map !== q.map) continue
    const d = sub(p.key, q.key)
    if (decide(d, path) === true && decide(scale(d, -1), path) === true) rows.push({lin: sub(v(p.name), v(q.name)), label: ''}, {lin: sub(v(q.name), v(p.name)), label: ''})
  }
  for (const name of names) rows.push({lin: {[name]: -1}, label: ''})
  return rows
}
const keyOf = (cell: string): Lin => {
  const inner = cell.slice(cell.indexOf('[') + 1, -1)
  const out: Lin = {}
  // Keys are canonical texts `name:coef` joined by ',' at the outer level; a name may itself be a cell with brackets.
  let depth = 0, start = 0
  const parts: string[] = []
  for (let i = 0; i <= inner.length; i++) {
    const ch = inner[i]
    if (ch === '[') depth++
    else if (ch === ']') depth--
    else if ((ch === ',' && depth === 0) || i === inner.length) { if (i > start) parts.push(inner.slice(start, i)); start = i + 1 }
  }
  for (const part of parts) { const at = part.lastIndexOf(':'); out[part.slice(0, at)] = Number(part.slice(at + 1)) }
  return out
}

// A leaf may also use the product of two of its rows: p <= 0 and q <= 0 give p·q >= 0, as nlinarith does. A pair may
// name an earlier product row too (index past the leaf's rows), which is a row of the same kind, so degrees go higher.
export function withProducts(rows: Constraint[], pairs: [number, number][]): Constraint[] {
  const out = [...rows]
  for (const [i, j] of pairs) {
    const p = out[i], q = out[j], pq = p && q ? times(p.lin, q.lin) : undefined
    out.push(pq ? {lin: scale(pq, -1), label: ''} : {lin: {}, label: ''})
  }
  return out
}

export function check(goal: Goal, tree: Tree, path: Path = new Map()): boolean {
  if ('leaf' in tree) return checkRefutation(withProducts(leafConstraints(goal, path), tree.products ?? []), tree.leaf)
  const id = canon(tree.split)
  if (path.has(id) || Object.keys(tree.split).every(key => key === '1')) return false
  const yes = new Map(path).set(id, {lin: tree.split, holds: true}), no = new Map(path).set(id, {lin: tree.split, holds: false})
  return check(goal, tree.yes, yes) && check(goal, tree.no, no)
}

// --- machines ----------------------------------------------------------------------------------------------------------

// Every constant and factor is a natural, so every value a machine computes is one (∸ truncates).
function natural(e: E): boolean {
  switch (e.op) {
    case 'var': return true
    case 'const': return Number.isInteger(e.value) && e.value >= 0
    case 'mul': return Number.isInteger(e.k) && e.k >= 0 && natural(e.a)
    case 'prod': return natural(e.a) && natural(e.b)
    case 'if': return naturalC(e.c) && natural(e.then) && natural(e.else)
    case 'get': return natural(e.key)
    case 'add': case 'sub': case 'min': case 'max': return natural(e.a) && natural(e.b)
    default: return unreachable(e)
  }
}
const naturalC = (c: C): boolean => c.op === 'flag' ? true : c.op === 'not' ? naturalC(c.x) : c.op === 'and' || c.op === 'or' ? c.xs.every(naturalC) : natural(c.a) && natural(c.b)

// Substitution: variables by terms, and each map read by what the map holds (the start's constant, or a write over the
// map before the step).
type Subst = {vars: Record<string, E>, maps: Record<string, (key: E) => E>, flags: Record<string, C>}
function substE(e: E, s: Subst): E {
  switch (e.op) {
    case 'var': return s.vars[e.name] ?? e
    case 'const': return e
    case 'mul': return {...e, a: substE(e.a, s)}
    case 'prod': return {...e, a: substE(e.a, s), b: substE(e.b, s)}
    case 'if': return {op: 'if', c: substC(e.c, s), then: substE(e.then, s), else: substE(e.else, s)}
    case 'get': { const key = substE(e.key, s); return s.maps[e.map] ? s.maps[e.map]!(key) : {op: 'get', map: e.map, key} }
    case 'add': case 'sub': case 'min': case 'max': return {...e, a: substE(e.a, s), b: substE(e.b, s)}
    default: return unreachable(e)
  }
}
function substC(c: C, s: Subst): C {
  if (c.op === 'flag') { const f = s.flags[c.name]; if (!f) throw new Error(`unknown flag ${c.name}`); return f }
  if (c.op === 'not') return {op: 'not', x: substC(c.x, s)}
  if (c.op === 'and' || c.op === 'or') return {op: c.op, xs: c.xs.map(y => substC(y, s))}
  return {...c, a: substE(c.a, s), b: substE(c.b, s)}
}
const mentions = (c: C, names: string[]): boolean => JSON.stringify(c).match(/"name":"([^"]+)"/g)?.some(m => names.includes(m.slice(8, -1))) ?? false
// A precondition reads the params and nothing else: no state, no request, no map.
const aboutParams = (c: C, params: string[]): boolean => !JSON.stringify(c).includes('"op":"get"') && (JSON.stringify(c).match(/"name":"([^"]+)"/g) ?? []).every(m => params.includes(m.slice(8, -1)))
const preOf = (o: {params: string[], pre?: C}): C[] => {
  if (o.pre && !(aboutParams(o.pre, o.params) && naturalC(o.pre))) throw new Error('a precondition reads only the params')
  return o.pre ? [o.pre] : []
}

// Instances: for each law that holds at every key, the keys (over the state before the step) the proof assumes it at.
export type Instances = Record<string, E[]>

// --- scope -----------------------------------------------------------------------------------------------------------

// Every name a machine reads is one it declares. A goal reads an undeclared name as one more free natural, so a proof
// would still be sound about the machine as written; but the runtimes have no value for it, so the proof would be about
// a machine that never runs. Refused here, before any goal is made.
type Reads = {vars: Set<string>, maps: Set<string>, flags: Set<string>}
function reads(t: E | C, out: Reads = {vars: new Set(), maps: new Set(), flags: new Set()}): Reads {
  switch (t.op) {
    case 'var': out.vars.add(t.name); break
    case 'const': break
    case 'get': out.maps.add(t.map); reads(t.key, out); break
    case 'flag': out.flags.add(t.name); break
    case 'not': reads(t.x, out); break
    case 'and': case 'or': for (const y of t.xs) reads(y, out); break
    case 'mul': reads(t.a, out); break
    case 'if': reads(t.c, out); reads(t.then, out); reads(t.else, out); break
    case 'add': case 'sub': case 'min': case 'max': case 'prod': case '<': case '<=': case '=': reads(t.a, out); reads(t.b, out); break
    default: unreachable(t)
  }
  return out
}
function inScope(what: string, ts: (E | C)[], vars: string[], maps: string[] = [], flags: string[] = []) {
  for (const t of ts) {
    const r = reads(t)
    for (const name of r.vars) if (!vars.includes(name)) throw new Error(`${what} reads ${name}, which it doesn't declare`)
    for (const map of r.maps) if (!maps.includes(map)) throw new Error(`${what} reads the map ${map}, which it doesn't declare`)
    for (const flag of r.flags) if (!flags.includes(flag)) throw new Error(`${what} reads the flag ${flag}, which it doesn't declare`)
  }
}
const distinct = (what: string, names: string[]) => { const seen = new Set<string>(); for (const name of names) { if (seen.has(name)) throw new Error(`${what} declares ${name} twice`); seen.add(name) } }

// A machine (without its history: historyMachine checks that and scopes the plain machine it makes) and its laws. The
// step reads params, inputs and the state before it; a flag reads the flags declared before it; a start value reads the
// params; a law reads the params, the state, the maps and its own key.
export function scope(m: Machine, laws: Law[] = []) {
  const state = Object.keys(m.state), maps = Object.keys(m.maps ?? {}), flags = Object.keys(m.step.flags ?? {})
  const names = [...m.params, ...m.inputs, ...state]
  distinct(m.name, [...names, ...maps])
  for (const name of Object.keys(m.step.state ?? {})) if (!state.includes(name)) throw new Error(`${m.name}'s step sets ${name}, which isn't in its state`)
  for (const map of Object.keys(m.step.maps ?? {})) if (!maps.includes(map)) throw new Error(`${m.name}'s step writes the map ${map}, which it doesn't declare`)
  inScope(`${m.name}'s start`, Object.values(m.state), m.params)
  Object.values(m.step.flags ?? {}).forEach((c, i) => inScope(`${m.name}'s flag ${flags[i]}`, [c], names, maps, flags.slice(0, i)))
  inScope(`${m.name}'s step`, [...Object.values(m.step.state ?? {}), ...Object.values(m.step.maps ?? {}).flatMap(w => [w.key, w.value])], names, maps, flags)
  if (m.assume) inScope(`${m.name}'s assumption`, [m.assume], names, maps, flags)
  if (m.pre) inScope(`${m.name}'s precondition`, [m.pre], m.params)
  distinct(`${m.name}'s laws`, laws.map(l => l.name))
  for (const law of laws) {
    if (law.forall && [...names, ...maps].includes(law.forall)) throw new Error(`law ${law.name}'s key ${law.forall} is already a name of ${m.name}`)
    inScope(`law ${law.name}`, [law.holds], [...m.params, ...state, ...(law.forall ? [law.forall] : [])], maps)
  }
}

// --- histories ---------------------------------------------------------------------------------------------------------

// A term or condition that reads only these names, and no map.
const readsOnly = (t: E | C, names: string[]): boolean => !JSON.stringify(t).includes('"op":"get"') && !JSON.stringify(t).includes('"op":"flag"') && (JSON.stringify(t).match(/"name":"([^"]+)"/g) ?? []).every(m => names.includes(m.slice(8, -1)))
const homogeneous = (e: E, names: string[]): boolean => e.op === 'var' ? names.includes(e.name) : e.op === 'add' ? homogeneous(e.a, names) && homogeneous(e.b, names) : e.op === 'mul' ? Number.isInteger(e.k) && e.k >= 0 && homogeneous(e.a, names) : false

// A machine with a history as a plain one: each sum a state variable from 0, plus its term at the request whenever the
// step keeps the request; each query an input; each relation part of the step's assumption. Sound because, at every
// step, a sum is the sum of its term over the history so far and a query the sum of its term over the same records:
// a relation that holds record by record (the goals returned, one per relation, over a record's fields as free
// naturals) holds of the sums, since a and b are linear without a constant and `when` doesn't read the record.
export function historyMachine(m: Machine): {machine: Machine, goals: Goal[]} {
  const h = m.history
  if (!h) return {machine: m, goals: []}
  const queries = Object.keys(h.queries), sums = Object.keys(h.sums), plainInputs = m.inputs.filter(i => !queries.includes(i))
  const fields = h.record.map(f => `r.${f}`)
  const taken = [...m.params, ...m.inputs, ...Object.keys(m.state), ...Object.keys(m.step.state ?? {})]
  // r.<field> names a record's field and nothing else: a param, input or state variable of that name would be read as
  // the field in the per-record goal and as itself in `pre` and `when`.
  const ok = [...taken, ...sums].every(name => !name.startsWith('r.'))
    && queries.every(q => m.inputs.includes(q)) && h.record.every(f => plainInputs.includes(f)) && sums.every(s => !taken.includes(s))
    && Object.values(h.sums).every(g => natural(g) && readsOnly(g, [...fields, ...m.params]))
    && Object.values(h.queries).every(g => natural(g) && readsOnly(g, [...fields, ...m.params, ...plainInputs])) && naturalC(h.keep)
    && (h.relations ?? []).every(r => naturalC(r.when) && readsOnly(r.when, [...m.params, ...plainInputs]) && r.holds.op === '<=' && homogeneous(r.holds.a, [...sums, ...queries]) && homogeneous(r.holds.b, [...sums, ...queries]))
  if (!ok) throw new Error('a history: sums read the record and params, queries also the request\'s other inputs, relations are homogeneous a <= b under a condition on the params and the request')
  inScope(`${m.name}'s keep`, [h.keep], [...m.params, ...m.inputs, ...Object.keys(m.state), ...sums], Object.keys(m.maps ?? {}), Object.keys(m.step.flags ?? {}))
  if (h.prune && !(h.record.includes(h.prune.order) && natural(h.prune.after) && readsOnly(h.prune.after, m.params))) throw new Error('a history is pruned by a recorded input and a term over the params')
  const atRequest: Subst = {vars: Object.fromEntries(h.record.map(f => [`r.${f}`, {op: 'var', name: f} as E])), maps: {}, flags: {}}
  const relations = (h.relations ?? []).map(r => ({op: 'or', xs: [{op: 'not', x: r.when}, r.holds]}) as C)
  const machine: Machine = {
    ...m, history: undefined,
    state: {...m.state, ...Object.fromEntries(sums.map(s => [s, {op: 'const', value: 0} as E]))},
    step: {...m.step, state: {...m.step.state, ...Object.fromEntries(sums.map(s => [s, {op: 'add', a: {op: 'var', name: s}, b: {op: 'if', c: h.keep, then: substE(h.sums[s]!, atRequest), else: {op: 'const', value: 0}}} as E]))}},
    ...(m.assume || relations.length ? {assume: {op: 'and', xs: [...(m.assume ? [m.assume] : []), ...relations]}} : {}),
  }
  const perRecord: Subst = {vars: {...h.sums, ...h.queries}, maps: {}, flags: {}}
  const goals = (h.relations ?? []).map((r, i) => ({name: `relation ${i + 1} @record`, hyps: [...preOf(m), r.when, {op: 'not', x: substC(r.holds, perRecord)} as C]}))
  // Pruning: a record whose order plus `after` is at most the request's adds nothing to any query. With requests in
  // nondecreasing order (the runtimes refuse one that goes back), such a record adds nothing to any later query either,
  // so dropping it changes no query: these goals are about the runtimes, the laws are proven over the whole history.
  if (h.prune) {
    const {order, after} = h.prune
    const gone: C = {op: '<=', a: {op: 'add', a: {op: 'var', name: `r.${order}`}, b: after}, b: {op: 'var', name: order}}
    for (const [q, g] of Object.entries(h.queries)) goals.push({name: `prune @query ${q}`, hyps: [...preOf(m), gone, {op: 'not', x: {op: '<=', a: g, b: {op: 'const', value: 0}}}]})
  }
  return {machine, goals}
}

export function obligations(m: Machine, laws: Law[], instances: Record<string, Instances> = {}): Goal[] {
  if (m.history) { const {machine, goals} = historyMachine(m); return [...obligations(machine, laws, instances), ...goals] }
  scope(m, laws)
  const ok = [...Object.values(m.state), ...Object.values(m.step.state ?? {}), ...Object.values(m.step.maps ?? {}).flatMap(w => [w.key, w.value])].every(natural)
    && Object.values(m.step.flags ?? {}).every(naturalC) && laws.every(l => naturalC(l.holds)) && Object.values(m.maps ?? {}).every(c => Number.isInteger(c) && c >= 0)
  if (!ok || laws.some(l => mentions(l.holds, m.inputs))) throw new Error('a negative constant or factor, or a law about a request, is outside the kernel')
  const fresh = (law: Law) => `${law.forall}#`
  const atKey = (law: Law, key: E): C => substC(law.holds, {vars: {[law.forall!]: key}, maps: {}, flags: {}})
  const goal = (law: Law) => (law.forall ? atKey(law, {op: 'var', name: fresh(law)}) : law.holds)
  const pre = preOf(m)
  // At the start: the precondition, and no request.
  const start: Subst = {vars: Object.fromEntries(Object.entries(m.state)), maps: Object.fromEntries(Object.entries(m.maps ?? {}).map(([map, c]) => [map, () => ({op: 'const', value: c})])), flags: {}}
  // One step: the state after, as terms over the state before; a map read after the step is the written value at the
  // written key, and the old cell elsewhere.
  const flags: Subst = {vars: {}, maps: {}, flags: m.step.flags ?? {}}
  const inline = (c: C) => substC(c, flags), inlineE = (e: E) => substE(e, flags)
  const step: Subst = {
    vars: Object.fromEntries(Object.entries(m.step.state ?? {}).map(([name, e]) => [name, inlineE(e)])),
    flags: {},
    maps: Object.fromEntries(Object.entries(m.step.maps ?? {}).map(([map, w]) => [map, (key: E): E => ({op: 'if', c: {op: '=', a: key, b: inlineE(w.key)}, then: inlineE(w.value), else: {op: 'get', map, key}})])),
  }
  const out: Goal[] = []
  for (const law of laws) {
    out.push({name: `${law.name} @start`, hyps: [...pre, {op: 'not', x: substC(goal(law), start)}]})
    const before = laws.flatMap(l => (l.forall ? (instances[law.name]?.[l.name] ?? []).map(key => atKey(l, key)) : [l.holds]))
    out.push({name: `${law.name} @step`, hyps: [...pre, ...(m.assume ? [inline(m.assume)] : []), ...before, {op: 'not', x: substC(goal(law), step)}]})
  }
  return out
}

// The whole set at once: every goal has a tree, and every tree checks.
export function checkLaws(m: Machine, laws: Law[], proof: {instances: Record<string, Instances>, trees: Record<string, Tree>}): boolean {
  return obligations(m, laws, proof.instances).every(g => proof.trees[g.name] !== undefined && check(g, proof.trees[g.name]!))
}

// --- loops: termination ------------------------------------------------------------------------------------------------

// A loop runs `body` while `while` holds; each turn may read fresh inputs (a server's delay, a page's size). It halts if a
// natural-valued rank, over the state and params, drops on every turn the invariants allow: naturals can't drop forever.
export type Loop = {name: string, params: string[], inputs: string[], state: Record<string, E>, while: C, body: Record<string, E>, pre?: C, assume?: C}

// A rank may be a tuple, compared in order (lexicographically): the first part drops, or it stays and the rest drops.
// Tuples of naturals can't drop forever either; nested loops need them (an outer count, then an inner one).
// A rank reads the state and params only: one that reads the turn's input drops against this turn's input, but the next
// turn measures it with a fresh one, so nothing need decrease (while x < w, x := x + 1, rank w ∸ x, w = x + 1 each turn).
export function loopObligations(l: Loop, laws: Law[], rank: E | E[]): Goal[] {
  const ranks = Array.isArray(rank) ? rank : [rank]
  const parts = [...Object.values(l.state), ...Object.values(l.body), ...ranks]
  const names = [...l.params, ...l.inputs, ...Object.keys(l.state)]
  distinct(l.name, names)
  for (const name of Object.keys(l.body)) if (!(name in l.state)) throw new Error(`${l.name}'s body sets ${name}, which isn't in its state`)
  inScope(`${l.name}'s start`, Object.values(l.state), l.params)
  inScope(l.name, [...Object.values(l.body), l.while, ...(l.assume ? [l.assume] : [])], names)
  inScope(`${l.name}'s precondition`, l.pre ? [l.pre] : [], l.params)
  inScope(`${l.name}'s rank and laws`, [...ranks, ...laws.map(law => law.holds)], [...l.params, ...Object.keys(l.state)])
  if (ranks.some(r => mentions({op: '=', a: r, b: r}, l.inputs))) throw new Error('a rank reads the state and params, not the turn\'s input')
  if (!parts.every(natural) || !naturalC(l.while) || !laws.every(law => !law.forall && naturalC(law.holds) && !mentions(law.holds, l.inputs))) throw new Error('outside the kernel')
  const start: Subst = {vars: l.state, maps: {}, flags: {}}, turn: Subst = {vars: l.body, maps: {}, flags: {}}
  const pre = preOf(l)
  const during = [...pre, ...(l.assume ? [l.assume] : []), l.while, ...laws.map(law => law.holds)]
  return [
    ...laws.flatMap(law => [
      {name: `${law.name} @start`, hyps: [...pre, {op: 'not', x: substC(law.holds, start)} as C]},
      {name: `${law.name} @turn`, hyps: [...during, {op: 'not', x: substC(law.holds, turn)} as C]},
    ]),
    {name: 'rank drops', hyps: [...during, {op: 'not', x: drops(ranks, turn)}]},
  ]
}

const drops = (ranks: E[], turn: Subst): C => {
  const [r, ...rest] = ranks
  const after = substE(r!, turn), less: C = {op: '<', a: after, b: r!}
  return rest.length === 0 ? less : {op: 'or', xs: [less, {op: 'and', xs: [{op: '=', a: after, b: r!}, drops(rest, turn)]}]}
}

// --- progress: laws with "there is a request" ----------------------------------------------------------------------

// "In every reachable state where `when` holds, some request makes `then` true of the step": proven by naming the
// request (a term per input over the state and params) and proving it allowed (the machine's assumption holds of it)
// and that the step it causes makes `then` hold. `then` reads the state before the step by plain names and after it by
// primed names (s', and M'[k] as a read of the map named M'). The laws assumed must be proven inductive on their own.
export function progressObligations(m: Machine, laws: Law[], instances: Instances, p: {name: string, when: C, then: C, request: Record<string, E>}): Goal[] {
  if (!m.inputs.every(i => i in p.request) || !Object.values(p.request).every(natural) || mentions(p.when, m.inputs)) throw new Error('outside the kernel')
  for (const e of Object.values(p.request)) if (mentions({op: '=', a: e, b: e}, m.inputs)) throw new Error('a request is named from the state and params')
  const req: Subst = {vars: p.request, maps: {}, flags: {}}
  const flags = Object.fromEntries(Object.entries(m.step.flags ?? {}).map(([f, c]) => [f, substC(c, req)]))
  const now = (e: E) => substE(substE(e, {vars: {}, maps: {}, flags: m.step.flags ?? {}}), req)
  const after: Subst = {
    vars: {...p.request, ...Object.fromEntries(Object.keys(m.state).map(n => [`${n}'`, {op: 'var', name: n} as E])), ...Object.fromEntries(Object.entries(m.step.state ?? {}).map(([n, e]) => [`${n}'`, now(e)]))},
    maps: {
      ...Object.fromEntries(Object.keys(m.maps ?? {}).map(map => [`${map}'`, (key: E): E => ({op: 'get', map, key})])),
      ...Object.fromEntries(Object.entries(m.step.maps ?? {}).map(([map, w]) => [`${map}'`, (key: E): E => ({op: 'if', c: {op: '=', a: key, b: now(w.key)}, then: now(w.value), else: {op: 'get', map, key}})])),
    },
    flags,
  }
  const before = [...preOf(m), ...laws.flatMap(l => (l.forall ? (instances[l.name] ?? []).map(key => substC(l.holds, {vars: {[l.forall!]: key}, maps: {}, flags: {}})) : [l.holds])), p.when]
  return [
    ...(m.assume ? [{name: `${p.name}: the request is allowed`, hyps: [...before, {op: 'not', x: substC(m.assume, req)} as C]}] : []),
    {name: `${p.name}: the step it causes`, hyps: [...before, {op: 'not', x: substC(p.then, after)}]},
  ]
}

// --- trees: structural induction ---------------------------------------------------------------------------------------

// A fold over binary trees whose leaves and nodes carry inputs: a leaf's state from its inputs, a node's from its
// children's (l_name, r_name) and its own inputs. A law holds of every tree if it holds at every leaf, and at a node
// whenever it holds at both children.
export type Fold = {name: string, params: string[], inputs: string[], leaf: Record<string, E>, node: Record<string, E>, pre?: C, assume?: C}

export function foldObligations(f: Fold, laws: Law[]): Goal[] {
  if (![...Object.values(f.leaf), ...Object.values(f.node)].every(natural) || !laws.every(law => !law.forall && naturalC(law.holds) && !mentions(law.holds, f.inputs))) throw new Error('outside the kernel')
  const names = Object.keys(f.leaf)
  distinct(f.name, [...f.params, ...f.inputs, ...names])
  if (Object.keys(f.node).sort().join() !== [...names].sort().join()) throw new Error(`${f.name}'s leaf and node set the same names`)
  inScope(`${f.name}'s leaf`, [...Object.values(f.leaf), ...(f.assume ? [f.assume] : [])], [...f.params, ...f.inputs])
  inScope(`${f.name}'s node`, Object.values(f.node), [...f.params, ...f.inputs, ...names.flatMap(n => [`l_${n}`, `r_${n}`])])
  inScope(`${f.name}'s precondition`, f.pre ? [f.pre] : [], f.params)
  inScope(`${f.name}'s laws`, laws.map(law => law.holds), [...f.params, ...names])
  const side = (p: string): Subst => ({vars: Object.fromEntries(names.map(n => [n, {op: 'var', name: `${p}${n}`} as E])), maps: {}, flags: {}})
  // A fold's inputs are each leaf's and node's own, so its assumption holds at every leaf and node it reads them at.
  const assume = [...preOf(f), ...(f.assume ? [f.assume] : [])]
  return laws.flatMap(law => [
    {name: `${law.name} @leaf`, hyps: [...assume, {op: 'not', x: substC(law.holds, {vars: f.leaf, maps: {}, flags: {}})} as C]},
    {name: `${law.name} @node`, hyps: [...assume, ...laws.flatMap(h => [substC(h.holds, side('l_')), substC(h.holds, side('r_'))]), {op: 'not', x: substC(law.holds, {vars: f.node, maps: {}, flags: {}})} as C]},
  ])
}
