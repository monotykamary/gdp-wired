// A TIP problem as a gdp-wired datatype law (core/data.ts): its datatypes declared by their constructors, its functions
// by their recursion (structural, or well-founded: core/data.ts finds a measure and proves every call lowers it before
// the function's equation is a fact), its goal a law. What is read, and how:
//   - A datatype is taken at each instance the problem uses (`list` at the naturals is its own datatype): the
//     instances whose fields reach each other are declared together (`mutual`), the rest in order. A datatype of the
//     shape of the naturals (no parameter, a constructor of no field and one of a single field of itself, Z and S) is
//     gdp-wired's natural: its constructors 0 and n + 1, a match on it a match on a natural. Same values, same statement.
//   - A polymorphic function is taken at each instance it is called at (monomorphisation of the functions: the goal is
//     about the instances it calls). A function with a function argument is taken at each function it is passed (a
//     lambda, specialised into the body, the variables it captures as further arguments; or a function variable of the
//     goal): the statement doesn't change. This is defunctionalisation with every closure known where it is applied:
//     each lambda a constructor of its own (its key), its captures its fields (the further arguments), `apply` the match
//     on it resolved in the body; TIP never stores a function in a field, returns one, or passes a new lambda to a call
//     that recurs, so no closure value is left to match at run time (core/data.ts's `closures` is that datatype, for
//     the library's users). A function of no argument is inlined.
//   - The goal's own sort variables (`par (a) ...`) and the uninterpreted sorts (`declare-sort S 0`) are abstract sorts
//     (core/data.ts's `opaque`, each its own): values read by equality alone, which TIP's typing gives (no polymorphic
//     function can order or add a value of a sort variable) and the library checks, so the law proven is the statement
//     at every sort, unchanged (core/data.ts says why). `--naturals` (solve.ts) takes them at the naturals instead.
//   - An uninterpreted constant or function (`declare-const`, `declare-fun`, at an instance of its sort variables) is an
//     unknown function of its arguments' sorts (core/data.ts's `unknownFn`; a constant one of none): the law is about
//     every value of it, as TIP's statement is about every model.
//   - A function variable of the goal from naturals to naturals is gdp-wired's `fnParam`; one from naturals to Bool is
//     x ↦ g(x) = 0 for an unknown g (every predicate is one of those, so the quantifier is the same); one of any other
//     sort (into a list, of an abstract sort, of several arguments) an unknown function of its sorts (`unknownFn`).
//   - Int: where the problem uses no subtraction, negative literal or product of two unknowns, read as a natural (each
//     operation means the same on the naturals, + and constant multiples, and div and mod by a positive constant, which
//     SMT-LIB and the naturals agree on there: a change of the statement, counted, since Int's variables and fields then
//     range over the naturals); otherwise as gdp-wired's integers (core/data.ts's `integer`, Lean's Int), the statement
//     unchanged: −, unary minus, constant multiples of any sign, div and mod by a positive constant (SMT-LIB's, Euclid's:
//     0 ≤ x mod k < k). A product of two unknowns is a product of naturals (`mul`) where Int is read as a natural, and
//     refused over the integers; division by anything but a positive constant is refused (nonlinear: x = y·q + r).
//   - What changes the statement, counted apart (`changes`): Int read as a natural (above); with `--naturals`, the goal's
//     own sort variables taken at the naturals (the law is then the instance at the naturals).
//   - A datatype field of sort Bool is a value of a datatype of two constructors of no field (false, true): built from
//     the condition where a constructor is applied, the condition again where a match binds it.
//   - An existential at the goal's end (∀ v. H ⇒ ∃ x. B): laws without it, each proven or refuted as a goal (`some`).
//   - Refused, with the reason (`Unsupported`): an existential elsewhere, a quantifier elsewhere than outermost or under an
//     implication's conclusion, a datatype field of a function sort, a function variable of a function or of an integer,
//     a function that returns a function, Int arithmetic beyond the above, a selector of a datatype of several
//     constructors (partial: TIP leaves it unspecified at the others), recursion whose termination core/data.ts doesn't
//     prove (no measure found and proven to fall at every call: `idiv x 0` never ends, and TIP's define-fun-rec doesn't
//     say so), nested recursion, a ring of functions whose termination isn't proven, an uninterpreted sort of arguments, an
//     uninterpreted constant at two sorts (TIP's evaluator gives a name one value), a nested datatype at ever larger
//     instances (no finite set of instances: monomorphisation doesn't end).
// The background facts a problem asserts (`assert`, true lemmas given as hints) aren't given to proveData: the statement
// is the goal alone.
import {type Sx, type Tip, type Ty, type V, BOOL, INT, Unsupported, existential, matchTy, prenex, sameTy, show, showTy, substSx, substTy, tyOf} from './tip.ts'
import {Bool, type Callable, Data, type DataLaw, Integer, Nat, type Sort, Val, type Value, boolean, data, define, evalX, fnParam, integer, law, mutual, natural, no, opaque, programOf, self, unknownFn, when, yes} from '../../core/data.ts'

const NATS: Ty = {k: 'con', name: '$Nat', args: []} // a type variable of the goal, at the naturals
const san = (s: string) => s.replace(/[^A-Za-z0-9]/g, c => `_${c.charCodeAt(0).toString(16)}`)

type DSL = Nat | Bool | Val | Integer
// A function value: a lambda (its captured bindings) or a function variable of the goal.
type Closure =
  | {k: 'lam', params: {name: string, ty: Ty}[], body: Sx, tsub: Map<string, Ty>, captures: Map<string, Bound>, key: string, ty: Ty}
  | {k: 'param', apply: (args: DSL[]) => DSL, key: string, ty: Ty}
type Bound = {v: DSL | Closure, ty: Ty}
type Env = {vars: Map<string, Bound>, tsub: Map<string, Ty>, raw?: boolean}
const isClosure = (v: DSL | Closure): v is Closure => !(v instanceof Nat || v instanceof Bool || v instanceof Val || v instanceof Integer)

export type Instance = {tipName: string, gdpName: string, inst: Ty[], argTys: Ty[], retTy: Ty, callable: Callable, specialised: boolean}
export type Translation = {
  law: DataLaw, tip: Tip, goal: Sx, changes: string[], notes: string[],
  // A function variable of the goal, or an uninterpreted constant or function (`const`): `eval`, its value as TIP's
  // evaluator reads it, at a sample's tables of the unknowns.
  vars: {gdp: string, tip: string, ty: Ty}[], params: {gdp: string, tip: string, ty: Ty, pred: boolean, const?: boolean, eval: (tables: Record<string, (n: number) => number>) => V}[],
  lemmas: DataLaw[], fns: Instance[], datas: number, toTip: (v: Value, ty: Ty) => V, fromTip: (v: V, ty: Ty) => number,
  // An existential goal's laws (`law` is the first of them): `weak`, what it says whatever the witness (refutes it),
  // `witnesses`, it with a witness in place (each proves it); each with the TIP goal it states.
  some?: {binders: string[], weak?: {law: DataLaw, sx: Sx}, witnesses: {law: DataLaw, sx: Sx, terms: string[]}[]},
}

// (The diagnostics `inline` and `native` of the first run are proveData's own now, core/transfer.ts: a function that
// isn't recursive unfolded, a recursive one that computes a built-in bridged to it once the bridge is proven.)
// `sorts`: the goal's sort variables as abstract sorts (each its own, read by equality alone: the statement for every
// sort), or at the naturals (the instance there, a change of the statement).
export function translate(tip: Tip, name: string, lemmas: Sx[] = [], opts: {sorts?: 'abstract' | 'naturals'} = {}): Translation {
  const abstractVars = (opts.sorts ?? 'abstract') === 'abstract'
  const changes = new Set<string>(), notes = new Set<string>()
  for (const [s2, n] of tip.sortArity) if (n > 0) throw new Unsupported(`an uninterpreted sort of ${n} arguments (${s2})`)
  // Int as the integers where a natural reading would change what an operation means (above).
  const literal = (x: Sx) => typeof x === 'string' && /^\d+$/.test(x)
  // A subtraction or a negation (a negative literal is one): what truncates on the naturals.
  const needsInt = (x: Sx): boolean => typeof x !== 'string' && (x[0] === '-' || x.some(needsInt))
  const ints = [...tip.funs.values()].some(f => needsInt(f.body)) || needsInt(tip.goal.body) || lemmas.some(needsInt)
  if (ints) notes.add('Int as the integers')
  // --- sorts
  const isPeano = (d: string) => {
    const dd = tip.datas.get(d)
    if (!dd || dd.params.length || dd.ctors.length !== 2) return false
    const [a, b] = [...dd.ctors].sort((x, y) => x.fields.length - y.fields.length)
    return a!.fields.length === 0 && b!.fields.length === 1 && sameTy(b!.fields[0]!.ty, {k: 'con', name: d, args: []})
  }
  const peanoParts = (d: string) => { const dd = tip.datas.get(d)!, zi = dd.ctors.findIndex(c => !c.fields.length); return {zero: dd.ctors[zi]!.name, succ: dd.ctors[1 - zi]!.name} }
  const insts = new Map<string, {data: Data, decl: {name: string, params: string[], ctors: {name: string, fields: {name: string, ty: Ty}[]}[]}, args: Ty[], ctorName: Map<string, string>, fieldName: Map<string, string>}>()
  let dataSeq = 0
  const fieldTys = (t: Ty & {k: 'con'}) => { const d = tip.datas.get(t.name)!, m = new Map(d.params.map((p, i) => [p, t.args[i]!])); return d.ctors.map(c => c.fields.map(f => substTy(f.ty, m))) }
  // An abstract sort (core/data.ts's `opaque`): an uninterpreted sort, or a sort variable of the goal (`$T_a`).
  const abstracts = new Map<string, Data>()
  const isAbstract = (t: Ty) => t.k === 'con' && !t.args.length && (t.name.startsWith('$T_') || tip.sortArity.has(t.name))
  const abstractOf = (key: string): Data => { let d = abstracts.get(key); if (!d) { d = opaque(`A${++dataSeq}_${san(key.replace(/^\$T_/, '')).slice(0, 30)}`); abstracts.set(key, d) } return d }
  const sortOf = (t: Ty): Sort => {
    if (t.k === 'var') throw new Error(`an unresolved sort variable ${t.name}`)
    if (t.k === 'fun') throw new Unsupported('a value of a function sort where a datatype value is needed')
    if (t.name === '$Nat') return natural
    if (isAbstract(t)) { notes.add(t.name.startsWith('$T_') ? 'the goal\'s sort variables as abstract sorts (equality only)' : 'an uninterpreted sort as an abstract sort (equality only)'); return abstractOf(t.name) }
    if (t.name === 'Int') { if (ints) return integer; changes.add('Int read as natural'); return natural }
    if (t.name === 'Bool') return boolean
    if (!tip.datas.has(t.name)) throw new Unsupported(`the sort ${t.name}`)
    if (isPeano(t.name)) { notes.add('Peano naturals as naturals'); return natural }
    return dataInst(t)
  }
  const fieldSortOk = (t: Ty) => {
    if (t.k === 'fun') throw new Unsupported('a datatype field of a function sort')
  }
  // A field of sort Bool: a value of a datatype of two constructors of no field (gdp-wired's fields are naturals or
  // datatype values), made a condition again where a match binds it.
  let boolD: (Data & Record<string, unknown>) | undefined
  const boolData = () => (boolD ??= (notes.add('a Bool field as a datatype of two constructors'), data('BoolField', {K_false: {}, K_true: {}}) as never))
  const isBoolTy = (t: Ty) => t.k === 'con' && t.name === 'Bool'
  const toField = (t: Ty, v: DSL): DSL => (isBoolTy(t) ? when(v as Bool, boolData().K_true as Val, boolData().K_false as Val) : v)
  const fromField = (t: Ty, v: DSL): DSL => (isBoolTy(t) ? (v as Val).is('K_true') : v)
  const dataInst = (t: Ty & {k: 'con'}): Data => {
    const key = showTy(t)
    const had = insts.get(key)
    if (had) return had.data
    // The instances reachable through fields that aren't naturals; those that reach t back are t's group.
    const reach = (from: Ty & {k: 'con'}): Map<string, Ty & {k: 'con'}> => {
      const seen = new Map<string, Ty & {k: 'con'}>(), todo = [from]
      while (todo.length) {
        const u = todo.pop()!
        for (const fs of fieldTys(u)) for (const f of fs) {
          fieldSortOk(f)
          if (f.k !== 'con' || ['Int', 'Bool', '$Nat'].includes(f.name) || isAbstract(f) || isPeano(f.name) || insts.has(showTy(f))) continue
          if (!tip.datas.has(f.name)) throw new Unsupported(`the sort ${f.name}`)
          const k = showTy(f)
          if (!seen.has(k)) { if (seen.size > 40) throw new Unsupported('a nested datatype at ever larger instances'); seen.set(k, f); todo.push(f) }
        }
      }
      return seen
    }
    const mine = reach(t)
    // Declare first what t reaches and doesn't reach t back.
    for (const [k, u] of mine) if (k !== key && !reach(u).has(key)) sortOf(u)
    const group = [t, ...[...mine.entries()].filter(([k, u]) => k !== key && !insts.has(k) && reach(u).has(key)).map(([, u]) => u)]
    const names = new Map(group.map(u => [showTy(u), `D${++dataSeq}_${san(showTy(u)).slice(0, 40)}`]))
    const decls: Record<string, Record<string, Record<string, unknown>>> = {}
    const meta = group.map(u => {
      const d = tip.datas.get(u.name)!, fts = fieldTys(u), ctorName = new Map<string, string>(), fieldName = new Map<string, string>()
      const decl: Record<string, Record<string, unknown>> = {}
      d.ctors.forEach((c, i) => {
        const cn = `K_${san(c.name)}`
        ctorName.set(cn, c.name)
        decl[cn] = Object.fromEntries(c.fields.map((f, j) => {
          const fn = `f${j}_${san(f.name)}`.slice(0, 40)
          fieldName.set(`${cn}.${fn}`, f.name)
          const ft = fts[i]![j]!, own = names.get(showTy(ft))
          const s = own ? (own === names.get(showTy(u)) && group.length === 1 ? self : own) : isBoolTy(ft) ? boolData() : sortOf(ft)
          return [fn, s]
        }))
      })
      decls[names.get(showTy(u))!] = decl
      return {u, d, ctorName, fieldName}
    })
    let made: Record<string, Data>
    try {
      made = group.length === 1 ? {[names.get(key)!]: data(names.get(key)!, decls[names.get(key)!]! as never)} : mutual(decls as never)
    } catch (e) { throw new Unsupported(`the datatype ${key}: ${(e as Error).message}`) }
    for (const m of meta) insts.set(showTy(m.u), {data: made[names.get(showTy(m.u))!]!, decl: m.d, args: m.u.args, ctorName: m.ctorName, fieldName: m.fieldName})
    if (group.length > 1) notes.add('datatypes declared together')
    return insts.get(key)!.data
  }

  // --- functions, at their instances
  const fns = new Map<string, Instance>()
  let fnSeq = 0
  const freeVars = (s: Sx, bound: Set<string>, out: Set<string>) => {
    if (typeof s === 'string') { if (!bound.has(s)) out.add(s); return }
    if (s[0] === 'lambda' || s[0] === 'forall' || s[0] === 'exists') { const b = new Set(bound); for (const p of s[1] as Sx[][]) b.add(p[0] as string); freeVars(s[2]!, b, out); return }
    if (s[0] === 'let') { const b = new Set(bound); for (const p of s[1] as Sx[][]) { freeVars(p[1]!, bound, out); b.add(p[0] as string) } freeVars(s[2]!, b, out); return }
    if (s[0] === 'match') {
      freeVars(s[1]!, bound, out)
      for (const c of s[2] as Sx[][]) { const b = new Set(bound); if (Array.isArray(c[0])) for (const v of c[0].slice(1)) b.add(v as string); freeVars(c[1]!, b, out) }
      return
    }
    if (s[0] === '_' || s[0] === 'as') { freeVars(s[1]!, bound, out); return }
    for (const x of s) freeVars(x, bound, out)
  }
  const closureKey = (c: Closure): string => c.k === 'param' ? `P(${c.key})` : c.key
  // A closure's captured values, flattened (each lambda's in order of name, nested closures' within).
  const capturedValues = (c: Closure): Bound[] => c.k === 'param' ? [] : [...c.captures.entries()].sort(([a], [b]) => (a < b ? -1 : 1)).flatMap(([, b]) => (isClosure(b.v) ? capturedValues(b.v) : [b]))
  // The same closure with its captured values replaced, in that order, by `vals`.
  const rebuild = (c: Closure, vals: DSL[]): Closure => {
    if (c.k === 'param') return c
    const caps = new Map<string, Bound>()
    for (const [n, b] of [...c.captures.entries()].sort(([a], [b2]) => (a < b2 ? -1 : 1))) caps.set(n, isClosure(b.v) ? {v: rebuild(b.v, vals), ty: b.ty} : {v: vals.shift()!, ty: b.ty})
    return {...c, captures: caps}
  }
  const instance = (fname: string, inst: Ty[], closures: (Closure | undefined)[], raw = false): Instance => {
    const fd = tip.funs.get(fname)!, key = `${fname}[${inst.map(showTy).join(',')}]{${closures.map(c => (c ? closureKey(c) : '-')).join(',')}}${raw ? 'raw' : ''}`
    const had = fns.get(key)
    if (had) return had
    const tsub = new Map(fd.params.map((p, i) => [p, inst[i]!]))
    const argTys = fd.args.map(a => substTy(a.ty, tsub)), retTy = substTy(fd.ret, tsub)
    if (retTy.k === 'fun') throw new Unsupported('a function that returns a function')
    const gdpName = `F${++fnSeq}_${san(fname)}`.slice(0, 48)
    const params: Record<string, Sort> = {}, plain: {i: number, pname: string}[] = [], extra: {pname: string, ty: Ty}[] = []
    fd.args.forEach((a, i) => { if (!closures[i]) { const pname = `a${i}_${san(a.name)}`.slice(0, 40); params[pname] = sortOf(argTys[i]!); plain.push({i, pname}) } })
    closures.forEach(c => { if (c) for (const b of capturedValues(c)) { const pname = `c${extra.length}`; params[pname] = sortOf(b.ty); extra.push({pname, ty: b.ty}) } })
    if (closures.some(Boolean)) notes.add('higher-order functions specialised at their function arguments')
    const callable: Callable = define(gdpName, params, sortOf(retTy), args => {
        const vars = new Map<string, Bound>()
        for (const p of plain) vars.set(fd.args[p.i]!.name, {v: args[p.pname] as DSL, ty: argTys[p.i]!})
        const vals = extra.map(e => args[e.pname] as DSL)
        closures.forEach((c, i) => { if (c) vars.set(fd.args[i]!.name, {v: rebuild(c, vals), ty: argTys[i]!}) })
        return value(emit(fd.body, {vars, tsub, raw}, retTy))
      })
    const out: Instance = {tipName: fname, gdpName, inst, argTys, retTy, callable, specialised: closures.some(Boolean)}
    fns.set(key, out)
    return out
  }
  const value = (b: Bound): DSL => { if (isClosure(b.v)) throw new Unsupported('a function value where a datatype value is needed'); return b.v }
  const natK = (n: number) => new Nat({op: 'nat', value: n})
  // An uninterpreted constant or function (declare-const, declare-fun) at an instance of its sort variables: an unknown
  // function of its arguments' sorts (core/data.ts's `unknownFn`; a constant one of no arguments, read at one key): the
  // law is then about every value of it, as TIP's statement is about every model. One instance of each (TIP's evaluator
  // gives a name one value).
  const unknowns: Translation['params'] = [], unknownAt = new Map<string, {u: ReturnType<typeof unknownFn>, at: string, retTy: Ty}>()
  const constApp = (cname: string, explicit: Ty[] | undefined, argSx: Sx[], env: Env, expected?: Ty): Bound => {
    const cd = tip.constDecls.get(cname)!
    if (argSx.length !== cd.args.length) throw new Unsupported(`${cname} applied to ${argSx.length} of its ${cd.args.length} arguments`)
    const vs = new Set(cd.params), m = new Map<string, Ty>()
    if (explicit) cd.params.forEach((q, i) => m.set(q, explicit[i]!))
    const args = argSx.map((a, i) => { const want = substTy(cd.args[i]!, m), b = emit(a, env, hasVars(want, vs) ? undefined : want); if (!matchTy(cd.args[i]!, b.ty, vs, m)) throw new Error(`${cname}: argument ${i} of sort ${showTy(b.ty)}`); return b })
    if (expected && cd.params.some(q => !m.has(q))) matchTy(cd.ret, expected, vs, m)
    if (cd.params.some(q => !m.has(q))) throw new Error(`${cname}: its sort variables unresolved`)
    const argTys = cd.args.map(t => substTy(t, m)), retTy = substTy(cd.ret, m), at = `${argTys.map(showTy).join(',')}->${showTy(retTy)}`
    let had = unknownAt.get(cname)
    if (had && had.at !== at) throw new Unsupported(`an uninterpreted constant at two sorts (${cname})`)
    if (!had) {
      const gdp = `k${unknowns.length + 1}_${san(cname)}`.slice(0, 40), u = unknownFn(gdp, argTys.map(sortOf), sortOf(retTy))
      had = {u, at, retTy}
      unknownAt.set(cname, had)
      notes.add('an uninterpreted constant as an unknown of its sort')
      unknowns.push({gdp, tip: cname, ty: argTys.length ? {k: 'fun', args: argTys, ret: retTy} : retTy, pred: false, const: true, eval: tables => (argTys.length ? {fn: (xs: V[]) => evalUnknown(u, argTys, retTy, xs, tables)} : evalUnknown(u, [], retTy, [], tables))})
    }
    return {v: had.u(...args.map(value)) as DSL, ty: retTy}
  }
  // An unknown's value at TIP's arguments, as TIP's: the term at variables, evaluated at a sample's tables.
  const evalUnknown = (u: ReturnType<typeof unknownFn>, argTys: Ty[], retTy: Ty, xs: V[], tables: Record<string, (n: number) => number>): V => {
    const vars = argTys.map((t, i) => wrapVar(sortOf(t), `$u${i}`)), out = u(...vars) as DSL
    return toTip(evalX(out instanceof Bool ? {op: 'bool', c: out.y} : out.x, new Map(argTys.map((t, i) => [`$u${i}`, toGdp(xs[i]!, t)])), tables), retTy)
  }
  const wrapVar = (s: Sort, n: string): DSL => (s === natural ? new Nat({op: 'var', name: n}) : s === boolean ? new Bool({op: 'holds', x: {op: 'var', name: n}}) : s === integer ? new Integer({op: 'var', name: n}) : new Val(s as Data, {op: 'var', name: n}))

  // --- terms
  const tyIn = (s: Sx, env: Env, extra: string[] = []) => substTy(tyOf(s, new Set([...env.tsub.keys(), ...extra])), env.tsub)
  const call = (fname: string, explicit: Ty[] | undefined, argSx: Sx[], env: Env, expected?: Ty): Bound => {
    const fd = tip.funs.get(fname)!
    if (argSx.length !== fd.args.length) throw new Unsupported(`${fname} applied to ${argSx.length} of its ${fd.args.length} arguments`)
    const vs = new Set(fd.params), m = new Map<string, Ty>()
    if (explicit) fd.params.forEach((p, i) => m.set(p, explicit[i]!))
    const args: Bound[] = []
    argSx.forEach((a, i) => {
      const want = substTy(fd.args[i]!.ty, m), b = emit(a, env, hasVars(want, vs) ? undefined : want)
      if (!matchTy(fd.args[i]!.ty, b.ty, vs, m)) throw new Error(`${fname}: argument ${i} of sort ${showTy(b.ty)}`)
      args.push(b)
    })
    if (expected && fd.params.some(p => !m.has(p))) matchTy(fd.ret, expected, vs, m)
    const unresolved = fd.params.filter(p => !m.has(p))
    if (unresolved.length) throw new Error(`${fname}: its sort variables ${unresolved.join(', ')} unresolved`)
    const inst = fd.params.map(p => m.get(p)!), retTy = substTy(fd.ret, m)
    if (!fd.args.length) return emit(fd.body, {vars: new Map(), tsub: new Map(fd.params.map((p, i) => [p, inst[i]!]))}, retTy)
    const closures = args.map(b => (isClosure(b.v) ? b.v : undefined))
    const ins = instance(fname, inst, closures, env.raw)
    const actual: (DSL)[] = [...args.filter(b => !isClosure(b.v)).map(b => b.v as DSL), ...closures.flatMap(c => (c ? capturedValues(c).map(value) : []))]
    return {v: ins.callable(...(actual as (Val | Nat | Bool | Integer)[])) as DSL, ty: retTy}
  }
  const hasVars = (t: Ty, vs: Set<string>): boolean => (t.k === 'var' ? vs.has(t.name) : t.k === 'con' ? t.args.some(a => hasVars(a, vs)) : t.args.some(a => hasVars(a, vs)) || hasVars(t.ret, vs))
  const ctorApp = (cname: string, explicit: Ty[] | undefined, argSx: Sx[], env: Env, expected?: Ty): Bound => {
    const {data: dname, index} = tip.ctorOf.get(cname)!, d = tip.datas.get(dname)!, c = d.ctors[index]!
    const vs = new Set(d.params), m = new Map<string, Ty>()
    if (explicit) d.params.forEach((p, i) => m.set(p, explicit[i]!))
    if (expected && expected.k === 'con' && expected.name === dname) d.params.forEach((p, i) => m.has(p) || m.set(p, expected.args[i]!))
    const args = argSx.map((a, i) => {
      const want = substTy(c.fields[i]!.ty, m), b = emit(a, env, hasVars(want, vs) ? undefined : want)
      if (!matchTy(c.fields[i]!.ty, b.ty, vs, m)) throw new Error(`${cname}: field ${i} of sort ${showTy(b.ty)}`)
      return toField(b.ty, value(b))
    })
    const unresolved = d.params.filter(p => !m.has(p))
    if (unresolved.length) throw new Error(`${cname}: its sort variables unresolved`)
    const ty: Ty = {k: 'con', name: dname, args: d.params.map(p => m.get(p)!)}
    if (isPeano(dname)) {
      const {zero} = peanoParts(dname)
      return {v: cname === zero ? natK(0) : (args[0] as Nat).plus(1), ty}
    }
    const D = dataInst(ty) as Data & Record<string, unknown>, k = `K_${san(cname)}`
    return {v: (args.length ? (D[k] as (...a: unknown[]) => Val)(...args) : D[k] as Val), ty}
  }
  const eqOf = (a: Bound, b: Bound): Bool => {
    const x = value(a), y = value(b)
    if (x instanceof Bool && y instanceof Bool) return x.iff(y)
    if (x instanceof Nat && y instanceof Nat) return x.eq(y)
    if (x instanceof Val && y instanceof Val) return x.eq(y)
    if (x instanceof Integer && y instanceof Integer) return x.eq(y)
    throw new Error('= of two sorts')
  }
  const arith = new Set(['+', '-', '*', 'div', 'mod', '<', '<=', '>', '>='])
  function emit(s: Sx, env: Env, expected?: Ty): Bound {
    if (typeof s === 'string') {
      const b = env.vars.get(s)
      if (b) return b
      if (s === 'true') return {v: yes, ty: BOOL}
      if (s === 'false') return {v: no, ty: BOOL}
      if (/^\d+$/.test(s)) {
        if (!Number.isSafeInteger(Number(s))) throw new Unsupported(`the numeral ${s}`)
        if (ints) return {v: new Integer({op: 'int', value: Number(s)}), ty: INT}
        changes.add('Int read as natural'); return {v: natK(Number(s)), ty: INT}
      }
      if (tip.ctorOf.has(s)) return ctorApp(s, undefined, [], env, expected)
      if (tip.constDecls.has(s)) return constApp(s, undefined, [], env, expected)
      if (tip.funs.has(s)) {
        const fd = tip.funs.get(s)!
        if (!fd.args.length) return call(s, undefined, [], env, expected)
        // a function passed by name: the lambda of its arguments
        if (fd.params.length) throw new Unsupported('a polymorphic function passed by name')
        const ps = fd.args.map((a, i) => [`$x${i}`, a.ty] as const)
        return emit(['lambda', ps.map(([n, t]) => [n, showTySx(t)]), [s, ...ps.map(([n]) => n)]], env, expected)
      }
      throw new Error(`unbound ${s}`)
    }
    const head = s[0]!
    if (Array.isArray(head) && (head[0] === '_' || head[0] === 'as')) {
      // (_ f T ..) applied to arguments
      const f = head[1] as string, ts = head.slice(2).map(t => tyIn(t, env))
      if (tip.ctorOf.has(f)) return ctorApp(f, ts, s.slice(1), env, expected)
      if (tip.constDecls.has(f)) return constApp(f, ts, s.slice(1), env, expected)
      if (tip.funs.has(f)) return call(f, ts, s.slice(1), env, expected)
      throw new Error(`instantiation of ${f}`)
    }
    if (typeof head !== 'string') throw new Error(`head ${show(head)}`)
    if (head === '_' || head === 'as') {
      const f = s[1] as string, ts = s.slice(2).map(t => tyIn(t, env))
      if (head === 'as') { const t = ts[0]!; return tip.ctorOf.has(f) ? ctorApp(f, undefined, [], env, t) : tip.constDecls.has(f) ? constApp(f, undefined, [], env, t) : call(f, undefined, [], env, t) }
      if (tip.ctorOf.has(f)) return ctorApp(f, ts, [], env, expected)
      if (tip.constDecls.has(f)) return constApp(f, ts, [], env, expected)
      return call(f, ts, [], env, expected)
    }
    if (arith.has(head)) {
      // div and mod by a positive constant (a literal): Euclid's on the integers, the naturals' own where Int is one.
      const divisor = (): number => {
        const d = s[2]
        if (s.length !== 3 || typeof d !== 'string' || !/^\d+$/.test(d) || Number(d) < 1 || !Number.isSafeInteger(Number(d))) throw new Unsupported(`Int arithmetic: ${head} by a term that isn't a positive constant (nonlinear)`)
        return Number(d)
      }
      const lits = s.slice(1).filter(literal).map(Number)
      if (!ints) {
        changes.add('Int read as natural')
        const xs = s.slice(1).map(x => value(emit(x, env, INT)) as Nat)
        if (head === '+') return {v: xs.reduce((a, b) => a.plus(b)), ty: INT}
        if (head === 'div' || head === 'mod') { const k = divisor(); return {v: head === 'div' ? xs[0]!.divBy(k) : xs[0]!.modBy(k), ty: INT} }
        if (head === '*') {
          const rest = s.slice(1).flatMap((x, i) => (literal(x) ? [] : [xs[i]!]))
          const k = lits.reduce((a, b) => a * b, 1)
          if (rest.length > 1) { notes.add('a product of two unknowns'); return {v: rest.slice(1).reduce((a, b) => a.mul(b), rest[0]!).times(k), ty: INT} }
          return {v: rest.length ? rest[0]!.times(k) : natK(k), ty: INT}
        }
        const [a, b] = xs as [Nat, Nat]
        return {v: head === '<' ? a.lt(b) : head === '<=' ? a.atMost(b) : head === '>' ? a.gt(b) : a.atLeast(b), ty: BOOL}
      }
      const xs = s.slice(1).map(x => value(emit(x, env, INT)) as Integer)
      if (head === '+') return {v: xs.reduce((a, b) => a.plus(b)), ty: INT}
      if (head === '-') return {v: xs.length === 1 ? xs[0]!.negate() : xs.slice(1).reduce((a, b) => a.minus(b), xs[0]!), ty: INT}
      if (head === 'div' || head === 'mod') { const k = divisor(); return {v: head === 'div' ? xs[0]!.divBy(k) : xs[0]!.modBy(k), ty: INT} }
      if (head === '*') {
        const rest = s.slice(1).flatMap((x, i) => (literal(x) ? [] : [xs[i]!]))
        if (rest.length > 1) throw new Unsupported('Int arithmetic: a product of two unknown integers')
        const k = lits.reduce((a, b) => a * b, 1)
        if (!Number.isSafeInteger(k)) throw new Unsupported('a coefficient too large')
        return {v: rest.length ? rest[0]!.times(k) : new Integer({op: 'int', value: k}), ty: INT}
      }
      const [a, b] = xs as [Integer, Integer]
      return {v: head === '<' ? a.lt(b) : head === '<=' ? a.atMost(b) : head === '>' ? a.gt(b) : a.atLeast(b), ty: BOOL}
    }
    switch (head) {
      case 'ite': {
        const c = value(emit(s[1]!, env, BOOL)) as Bool, a = emit(s[2]!, env, expected), b = emit(s[3]!, env, expected ?? a.ty)
        return {v: when(c, value(a) as never, value(b) as never) as DSL, ty: a.ty}
      }
      case 'and': case 'or': {
        const xs = s.slice(1).map(x => value(emit(x, env, BOOL)) as Bool)
        if (!xs.length) return {v: head === 'and' ? yes : no, ty: BOOL}
        return {v: xs.length === 1 ? xs[0]! : head === 'and' ? xs[0]!.and(...xs.slice(1)) : xs[0]!.or(...xs.slice(1)), ty: BOOL}
      }
      case 'not': return {v: (value(emit(s[1]!, env, BOOL)) as Bool).not(), ty: BOOL}
      case '=>': { const xs = s.slice(1).map(x => value(emit(x, env, BOOL)) as Bool); return {v: xs.slice(0, -1).reduceRight((acc, h) => h.implies(acc), xs.at(-1)!), ty: BOOL} }
      case '=': case 'distinct': {
        const first = emit(s[1]!, env), xs = [first, ...s.slice(2).map(x => emit(x, env, first.ty))]
        if (xs.some(b => isClosure(b.v))) throw new Unsupported('equality of functions')
        const pairs: Bool[] = []
        if (head === '=') for (let i = 1; i < xs.length; i++) pairs.push(eqOf(xs[0]!, xs[i]!))
        else for (let i = 0; i < xs.length; i++) for (let j = i + 1; j < xs.length; j++) pairs.push(eqOf(xs[i]!, xs[j]!).not())
        return {v: pairs.length === 1 ? pairs[0]! : pairs[0]!.and(...pairs.slice(1)), ty: BOOL}
      }
      case 'let': {
        const vars = new Map(env.vars)
        for (const b of s[1] as Sx[][]) vars.set(b[0] as string, emit(b[1]!, env))
        return emit(s[2]!, {vars, tsub: env.tsub, raw: env.raw}, expected)
      }
      case 'lambda': {
        const params = (s[1] as Sx[][]).map(b => ({name: b[0] as string, ty: tyIn(b[1]!, env)}))
        const fv = new Set<string>()
        freeVars(s, new Set(), fv)
        const captures = new Map<string, Bound>()
        for (const v of fv) { const b = env.vars.get(v); if (b) captures.set(v, b) }
        const key = `L(${show(s)}|${[...env.tsub.entries()].map(([k, t]) => `${k}=${showTy(t)}`).join(',')}|${[...captures.entries()].sort(([a], [b]) => (a < b ? -1 : 1)).map(([n, b]) => `${n}:${isClosure(b.v) ? closureKey(b.v) : showTy(b.ty)}`).join(',')})`
        // its sort: the body's at its parameters (a dry run of the body, for the sort alone)
        const probe = new Map(env.vars)
        for (const p of params) probe.set(p.name, p.ty.k === 'fun' ? {v: {k: 'param', apply: ([x]) => x!, key: '?', ty: p.ty}, ty: p.ty} : {v: dryValue(p.ty), ty: p.ty})
        const ret = emit(s[2]!, {vars: probe, tsub: env.tsub, raw: env.raw}).ty
        const ty: Ty = {k: 'fun', args: params.map(p => p.ty), ret}
        return {v: {k: 'lam', params, body: s[2]!, tsub: env.tsub, captures, key, ty}, ty}
      }
      case '@': {
        const f = emit(s[1]!, env), args = s.slice(2).map(x => emit(x, env))
        return apply(f, args)
      }
      case 'match': return matchOn(s, env, expected)
      case 'forall': case 'exists': throw new Unsupported('a quantifier inside a term')
    }
    if (tip.ctorOf.has(head)) return ctorApp(head, undefined, s.slice(1), env, expected)
    if (tip.selectorOf.has(head)) {
      const sel = tip.selectorOf.get(head)!, d = tip.datas.get(sel.data)!
      if (d.ctors.length > 1) throw new Unsupported('a selector of a datatype of several constructors (partial)')
      const of = emit(s[1]!, env), c = d.ctors[0]!
      return matchOn(['match', '$scrut', [[[c.name, ...c.fields.map((_, i) => `$s${i}`)], `$s${sel.field}`]]], {vars: new Map([...env.vars, ['$scrut', of]]), tsub: env.tsub, raw: env.raw}, expected)
    }
    if (head.startsWith('is-') && tip.ctorOf.has(head.slice(3))) {
      const cn = head.slice(3), of = emit(s[1]!, env), {data: dn} = tip.ctorOf.get(cn)!
      if (isPeano(dn)) { const n = value(of) as Nat; return {v: cn === peanoParts(dn).zero ? n.eq(0) : n.atLeast(1), ty: BOOL} }
      return {v: (value(of) as Val).is(`K_${san(cn)}`), ty: BOOL}
    }
    if (env.vars.has(head)) return apply(env.vars.get(head)!, s.slice(1).map(x => emit(x, env)))
    if (tip.constDecls.has(head)) return constApp(head, undefined, s.slice(1), env, expected)
    if (tip.funs.has(head)) return call(head, undefined, s.slice(1), env, expected)
    throw new Error(`unknown ${head}`)
  }
  function dryValue(t: Ty): DSL {
    const s = sortOf(t)
    return s === natural ? new Nat({op: 'var', name: '$dry'}) : s === boolean ? new Bool({op: 'holds', x: {op: 'var', name: '$dry'}}) : s === integer ? new Integer({op: 'var', name: '$dry'}) : new Val(s as Data, {op: 'var', name: '$dry'})
  }
  function apply(f: Bound, args: Bound[]): Bound {
    if (!isClosure(f.v)) throw new Error('application of a value')
    const c = f.v
    if (c.k === 'param') {
      const ft = c.ty as Ty & {k: 'fun'}
      if (args.length !== ft.args.length) throw new Unsupported('a function variable applied to fewer or more arguments than it takes')
      return {v: c.apply(args.map(value)), ty: ft.ret}
    }
    const n = Math.min(c.params.length, args.length), vars = new Map(c.captures)
    c.params.slice(0, n).forEach((p, i) => vars.set(p.name, args[i]!))
    if (n < c.params.length) throw new Unsupported('a lambda applied to fewer arguments than it takes')
    const out = emit(c.body, {vars, tsub: c.tsub})
    return args.length > n ? apply(out, args.slice(n)) : out
  }
  function matchOn(s: Sx[], env: Env, expected?: Ty): Bound {
    const of = emit(s[1]!, env), cases = s[2] as Sx[][]
    if (of.ty.k !== 'con' || !tip.datas.has(of.ty.name)) throw new Unsupported(`a match on ${showTy(of.ty)}`)
    const dn = of.ty.name, d = tip.datas.get(dn)!, fts = fieldTys(of.ty as Ty & {k: 'con'})
    const caseFor = (cn: string) => cases.find(c => (typeof c[0] === 'string' ? c[0] : (c[0] as Sx[])[0]) === cn) ?? cases.find(c => c[0] === '_')
    let ty: Ty | undefined = expected
    const body = (cn: string, fields: DSL[]): DSL => {
      const c = caseFor(cn)
      if (!c) throw new Error(`no case ${cn}`)
      const vars = new Map(env.vars), ci = d.ctors.findIndex(k => k.name === cn)
      if (Array.isArray(c[0])) c[0].slice(1).forEach((b, i) => vars.set(b as string, {v: fromField(fts[ci]![i]!, fields[i]!), ty: fts[ci]![i]!}))
      const out = emit(c[1]!, {vars, tsub: env.tsub, raw: env.raw}, ty)
      ty ??= out.ty
      return value(out)
    }
    if (isPeano(dn)) {
      const {zero, succ} = peanoParts(dn)
      const v = (value(of) as Nat).match({zero: () => body(zero, []), succ: ({pred}) => body(succ, [pred])}) as DSL
      return {v, ty: ty!}
    }
    const v = (value(of) as Val).match(Object.fromEntries(d.ctors.map(c => [`K_${san(c.name)}`, (fs: Record<string, DSL>) => body(c.name, c.fields.map((f, j) => fs[`f${j}_${san(f.name)}`.slice(0, 40)]!))]))) as DSL
    return {v, ty: ty!}
  }
  const showTySx = (t: Ty): Sx => (t.k === 'var' ? t.name : t.k === 'con' ? (t.args.length ? [t.name, ...t.args.map(showTySx)] : t.name) : ['=>', ...t.args.map(showTySx), showTySx(t.ret)])

  // --- the goal (and lemmas given to try, the same way)
  const lawOf = (lname: string, gparams: string[], body: Sx) => {
    const g = prenex(body)
    const tsub = new Map(gparams.map(p => [p, abstractVars ? {k: 'con', name: `$T_${p}`, args: []} as Ty : NATS]))
    const vars: Translation['vars'] = [], params: Translation['params'] = [], sorts: Record<string, Sort> = {}
    const fnVars = new Map<string, Closure>()
    for (const v of g.vars) {
      const ty = substTy(tyOf(v.ty, new Set(gparams)), tsub)
      if (ty.k === 'fun') {
        const natLike = (t: Ty) => t.k === 'con' && (t.name === '$Nat' || isPeano(t.name) || t.name === 'Int')
        const gdp = `p_${san(v.name)}`
        if (ty.args.length === 1 && natLike(ty.args[0]!) && (natLike(ty.ret) || (ty.ret.k === 'con' && ty.ret.name === 'Bool'))) {
          if (ints && [ty.args[0]!, ty.ret].some(t => t.k === 'con' && t.name === 'Int')) throw new Unsupported('a function variable over the integers')
          for (const t of [ty.args[0]!, ty.ret]) if (t.k === 'con' && t.name === 'Int') changes.add('Int read as natural')
          const pred = ty.ret.k === 'con' && ty.ret.name === 'Bool'
          if (pred) notes.add('a predicate variable p as x ↦ g(x) = 0')
          const f = fnParam(gdp)
          fnVars.set(v.name, {k: 'param', apply: ([x]) => (pred ? f(x as Nat).eq(0) : f(x as Nat)), key: gdp, ty})
          params.push({gdp, tip: v.name, ty, pred, eval: tables => ({fn: ([x]) => { const y = tables[gdp]!(fromTip(x!, ty.args[0]!)); return pred ? y === 0 : toTip(y, ty.ret) }})})
          continue
        }
        // Any other: an unknown function of its arguments' sorts (core/data.ts's `unknownFn`: one unknown of a natural read
        // at its arguments' keys, a datatype's value decoded from it), every function of that sort one of those.
        if (ty.args.some(t => t.k === 'fun') || ty.ret.k === 'fun') throw new Unsupported(`a function variable of sort ${showTy(ty)}`)
        if (ints && ty.args.some(t => t.k === 'con' && t.name === 'Int')) throw new Unsupported('a function variable of an integer')
        let u: ReturnType<typeof unknownFn>
        try { u = unknownFn(gdp, ty.args.map(sortOf), sortOf(ty.ret)) } catch (e) { throw new Unsupported(`a function variable of sort ${showTy(ty)}: ${(e as Error).message}`) }
        notes.add('a function variable as an unknown function, its results decoded from an unknown of a natural')
        fnVars.set(v.name, {k: 'param', apply: xs => u(...xs) as DSL, key: gdp, ty})
        params.push({gdp, tip: v.name, ty, pred: false, eval: tables => ({fn: (xs: V[]) => evalUnknown(u, ty.args, ty.ret, xs, tables)})})
        continue
      }
      const gdp = `v_${san(v.name)}`
      sorts[gdp] = sortOf(ty)
      vars.push({gdp, tip: v.name, ty})
    }
    let l: DataLaw
    try {
      l = law(lname, sorts, vs => {
        const env = new Map<string, Bound>()
        for (const v of vars) env.set(v.tip, {v: vs[v.gdp] as DSL, ty: v.ty})
        for (const [n, c] of fnVars) env.set(n, {v: c, ty: c.ty})
        const out = value(emit(g.body, {vars: env, tsub}, BOOL))
        if (!(out instanceof Bool)) throw new Error('the goal is not a condition')
        return out
      })
      // Every body read (each emitted, the instances they call made) and every recursion checked.
      programOf([l])
    } catch (e) {
      if (e instanceof Unsupported) throw e
      const m = (e as Error).message
      if (/, in its ring /.test(m)) throw new Unsupported(`a ring of functions that isn't structural recursion: ${m}`)
      if (/nested recursion/.test(m)) throw new Unsupported(`nested recursion: ${m}`)
      if (/not structural recursion/.test(m)) throw new Unsupported(`recursion whose termination isn't proven: ${m}`)
      throw e
    }
    return {law: l, vars, params, body: g.body}
  }
  if (tip.goal.params.length && !abstractVars) changes.add(`monomorphised: the goal's sort variable${tip.goal.params.length > 1 ? 's' : ''} ${tip.goal.params.join(', ')} at the naturals`)
  // An existential goal, ∀ v. H ⇒ ∃ x. B (core/exists.ts's "there exists", where proveData has no law for it): proven
  // through a witness among the goal's own variables of x's sort (H ⇒ B with it in place, a law of its own), and
  // refuted through what B says whatever x is, its conjuncts that read no x (W: ∃ x. B implies W, so a counterexample
  // to H ⇒ W is one to the goal). Each is a goal without a quantifier, translated as any goal is.
  const ex = existential(tip.goal.body)
  let some: Translation['some']
  if (ex) {
    const names = new Set(ex.binders.map(b => b.name)), reads = (c: Sx) => { const out = new Set<string>(); freeVars(c, new Set(), out); return [...out].some(n => names.has(n)) }
    const conj = (b: Sx): Sx[] => (Array.isArray(b) && b[0] === 'and' ? b.slice(1).flatMap(conj) : [b])
    const free = conj(ex.body).filter(c => !reads(c))
    const weakSx = free.length ? ex.with(free.length === 1 ? free[0]! : ['and', ...free]) : undefined
    const outer = prenex(ex.with('true')).vars
    const options = ex.binders.map(b => outer.filter(v => JSON.stringify(v.ty) === JSON.stringify(b.ty)).map(v => v.name))
    const combos = options.reduce<string[][]>((acc, os) => acc.flatMap(a => os.map(o => [...a, o])), [[]]).slice(0, 8)
    const witnesses = combos.filter(c => c.length === ex.binders.length).map(ts => {
      const sx = ex.with(ex.binders.reduce<Sx>((b, x, i) => substSx(b, x.name, ts[i]!), ex.body))
      return {law: lawOf(`${name} with ${ex.binders.map((x, i) => `${x.name} := ${ts[i]}`).join(', ')}`, tip.goal.params, sx).law, sx, terms: ts}
    })
    if (!weakSx && !witnesses.length) throw new Unsupported('an existential goal with no witness among its variables and nothing it says whatever the witness')
    some = {binders: ex.binders.map(b => b.name), ...(weakSx ? {weak: {law: lawOf(`${name}, whatever the witness`, tip.goal.params, weakSx).law, sx: weakSx}} : {}), witnesses}
    notes.add('an existential goal: refuted through what it says whatever the witness, proven through a witness among its variables')
  }
  const main = lawOf(name, tip.goal.params, ex ? (some!.weak?.sx ?? some!.witnesses[0]!.sx) : tip.goal.body)
  const extra = lemmas.map((x, i) => {
    const t = Array.isArray(x) && x[0] === 'par' ? {params: x[1] as string[], body: x[2]!} : {params: [], body: x}
    return lawOf(`lemma ${i + 1}`, t.params, t.body).law
  })
  const {law: l, vars, params} = main, g = main
  // --- values back to TIP's (for the evaluator)
  function toTip(v: Value, ty: Ty): V {
    if (ty.k !== 'con') throw new Error('a function value')
    if (ty.name === '$Nat' || ty.name === 'Int') return BigInt(v as number)
    // (an abstract value: its code, TIP's evaluator's value of an uninterpreted sort or a sort variable)
    if (isAbstract(ty)) return BigInt((v as {f: number[]}).f[0]!)
    if (ty.name === 'Bool') return typeof v === 'object' ? boolData().ctors[v.c]!.name === 'K_true' : v === 1
    if (isPeano(ty.name)) {
      const {zero, succ} = peanoParts(ty.name)
      let out: V = {c: zero, a: []}
      for (let i = 0; i < (v as number); i++) out = {c: succ, a: [out]}
      return out
    }
    const ins = insts.get(showTy(ty))!, o = v as {c: number, f: Value[]}, c = ins.data.ctors[o.c]!
    const tipC = ins.ctorName.get(c.name)!, fts = fieldTys(ty)[tip.datas.get(ty.name)!.ctors.findIndex(k => k.name === tipC)]!
    return {c: tipC, a: o.f.map((x, i) => toTip(x, fts[i]!))}
  }
  // TIP's value as the translation's (toTip's inverse).
  function toGdp(v: V, ty: Ty): Value {
    if (ty.k !== 'con') throw new Error('a function value')
    if (typeof v === 'bigint') return isAbstract(ty) ? {c: 0, f: [Number(v)]} : Number(v)
    if (typeof v === 'boolean') return +v
    if ('fn' in v) throw new Error('a function value')
    if (isPeano(ty.name)) return fromTip(v, ty)
    const ins = insts.get(showTy(ty))
    if (!ins) throw new Error(`no instance ${showTy(ty)}`)
    const j = ins.data.ctors.findIndex(c => ins.ctorName.get(c.name) === v.c), fts = fieldTys(ty)[tip.datas.get(ty.name)!.ctors.findIndex(k => k.name === v.c)]!
    return {c: j, f: v.a.map((x, i) => (isBoolTy(fts[i]!) ? {c: boolData().ctors.findIndex(c => c.name === (x === true ? 'K_true' : 'K_false')), f: []} : toGdp(x, fts[i]!)))}
  }
  function fromTip(v: V, ty: Ty): number {
    if (typeof v === 'bigint') return Number(v)
    if (ty.k === 'con' && isPeano(ty.name)) { let n = 0, x = v as {c: string, a: V[]}; while (x.a.length) { n++; x = x.a[0] as {c: string, a: V[]} } return n }
    throw new Error('not a natural')
  }
  return {law: l, tip, goal: g.body, changes: [...changes], notes: [...notes], vars, params: [...params, ...unknowns], lemmas: extra, fns: [...fns.values()], datas: insts.size, toTip, fromTip, ...(some ? {some} : {})}
}
