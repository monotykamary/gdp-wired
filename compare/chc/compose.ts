// A linear CHC system with its chains composed away (large-block encoding), before the rule is built: a predicate with
// no clause from itself to itself whose incoming clauses (heads) times its outgoing ones (bodies) are no more than the
// two together is eliminated, each pair of an incoming and an outgoing clause made one clause (the variables of each
// renamed apart, the outgoing clause's body arguments equal to the incoming clause's head arguments), until no
// predicate is left to eliminate. Every predicate stays declared, in its order (so the rule's locations and slots are
// the original's, and a law of the composed rule reads the same names as one of the original's); the eliminated have
// no clause.
//
// Nothing here is trusted. Each composed clause records the original clauses it is made of and, for each, the name its
// variables have in the composed clause (`parts`), so a model of the composed clause's variables is a model of each
// original clause's: an unsat derivation of the composed system is a derivation of the original's (`expand`), checked
// step by step against the original CHC (translate.ts's checkDerivation). A sat answer is a set of laws of the
// composed rule, read back for the original rule (`lift`): at a location the composition kept, the laws as they are;
// at an eliminated one, the composed laws after each clause out of it (its weakest precondition, over the original
// clauses), which the kernel then proves of the original rule.
import type {Chc, Clause, Sort, Sx} from './chc.ts'
import {type Built, type Raw, type Step, build, envOf} from './translate.ts'
import {type C, type E, type Law, type Machine, arithmetic, divisorsIn} from '../../core/machine.ts'
import {cutInterpolant} from '../../core/interp.ts'
import {substC, substE} from '../../kernel/kernel.ts'
import {simpC, simpE} from '../../core/nonterm.ts'
import {withDeadline} from '../../kernel/prove.ts'
import {proveRule} from '../../core/dsl.ts'

export type Part = {clause: number, ren: Map<string, string>}
// `steps`: each predicate eliminated, in order, with the clauses into it and out of it at that time (what `lift` reads)
export type Composed = {chc: Chc, parts: Part[][], eliminated: string[], steps: {pred: string, into: Clause[], out: Clause[]}[]}
export type ComposeOptions = {
  // a predicate is eliminated only where every clause out of it at that time leaves no variable to the request
  // (the weakest precondition is then a condition of the state alone; see `lift`)
  determined?: (c: Clause) => boolean
  maxConjuncts?: number // a composed clause's constraint at most this many conjuncts (200)
  maxClauses?: number // the system at most this many clauses (2x the original's, and at least 64)
}

// The symbols of an S-expression renamed (a let's own binders kept).
function renameSx(s: Sx, ren: Map<string, string>): Sx {
  if (typeof s === 'string') return ren.get(s) ?? s
  if (s[0] === 'let') {
    const inner = new Map(ren)
    for (const b of s[1] as Sx[][]) inner.delete(b[0] as string)
    return ['let', (s[1] as Sx[][]).map(b => [b[0]!, renameSx(b[1]!, ren)]), renameSx(s[2]!, inner)]
  }
  return s.map((x, i) => (i === 0 ? x : renameSx(x, ren)))
}

export function compose(chc: Chc, opts: ComposeOptions = {}): Composed {
  const maxConj = opts.maxConjuncts ?? 200, maxClauses = opts.maxClauses ?? Math.max(64, 2 * chc.clauses.length)
  let fresh = 0
  // A clause with its variables renamed apart: its parts' renamings composed with the fresh names.
  type Item = {clause: Clause, parts: Part[]}
  const apart = (it: Item): Item => {
    const ren = new Map<string, string>(), vars = new Map<string, Sort>()
    for (const [v, s] of it.clause.vars) { const n = `${v.split('!')[0]}!${fresh++}`; ren.set(v, n); vars.set(n, s) }
    const c = it.clause
    return {
      clause: {vars, body: c.body.map(a => ({pred: a.pred, args: a.args.map(x => renameSx(x, ren))})), constraint: c.constraint.map(x => renameSx(x, ren)), head: c.head && {pred: c.head.pred, args: c.head.args.map(x => renameSx(x, ren))}},
      parts: it.parts.map(p => ({clause: p.clause, ren: new Map([...p.ren].map(([o, n]) => [o, ren.get(n) ?? n]))})),
    }
  }
  // c1 into c2: c1's head is c2's body.
  const join = (a: Item, b: Item): Item => {
    const x = apart(a), y = apart(b), h = x.clause.head!, body = y.clause.body[0]!
    const eqs: Sx[] = body.args.map((arg, j) => ['=', arg, h.args[j]!])
    return {
      clause: {vars: new Map([...x.clause.vars, ...y.clause.vars]), body: x.clause.body, constraint: [...x.clause.constraint, ...eqs, ...y.clause.constraint], head: y.clause.head},
      parts: [...x.parts, ...y.parts],
    }
  }
  let items: Item[] = chc.clauses.map((clause, i) => ({clause, parts: [{clause: i, ren: new Map([...clause.vars.keys()].map(v => [v, v]))}]}))
  const eliminated: string[] = [], steps: Composed['steps'] = []
  if (chc.clauses.some(c => c.body.length > 1)) return {chc, parts: items.map(i => i.parts), eliminated, steps}
  for (;;) {
    let best: {p: string, score: number} | undefined
    for (const p of chc.preds.keys()) {
      if (eliminated.includes(p)) continue
      const into = items.filter(it => it.clause.head?.pred === p), out = items.filter(it => it.clause.body[0]?.pred === p)
      if (!into.length && !out.length) continue
      if (into.some(it => it.clause.body[0]?.pred === p)) continue
      const score = into.length * out.length - into.length - out.length
      if (score > 0) continue
      if (opts.determined && !out.every(it => opts.determined!(it.clause))) continue
      if (items.length + score > maxClauses) continue
      if (into.some(a => out.some(b => a.clause.constraint.length + b.clause.constraint.length + b.clause.body[0]!.args.length > maxConj))) continue
      if (!best || score < best.score) best = {p, score}
    }
    if (!best) break
    const p = best.p, into = items.filter(it => it.clause.head?.pred === p), out = items.filter(it => it.clause.body[0]?.pred === p)
    items = [...items.filter(it => !into.includes(it) && !out.includes(it)), ...into.flatMap(a => out.map(b => join(a, b)))]
    eliminated.push(p)
    steps.push({pred: p, into: into.map(i => used(i.clause)), out: out.map(i => used(i.clause))})
  }
  return {chc: {preds: chc.preds, clauses: items.map(i => used(i.clause))}, parts: items.map(i => i.parts), eliminated, steps}
}

// A clause's variables that it reads (one it declares and never reads is no value the request need bring).
function used(c: Clause): Clause {
  const seen = new Set<string>()
  for (const s of [...c.constraint, ...c.body.flatMap(a => a.args), ...(c.head?.args ?? [])]) for (const v of varsOf(s)) seen.add(v)
  return [...c.vars.keys()].every(v => seen.has(v)) ? c : {...c, vars: new Map([...c.vars].filter(([v]) => seen.has(v)))}
}

// --- the cone of influence ---------------------------------------------------------------------------------------------
//
// A system weakened where nothing it decides depends: each clause's definitions (x = e, x a variable no other conjunct,
// no body argument and nothing else reads but the head) of what no guard, no query and no other relevant value ever
// reads dropped, so that value is the request's (any) there. A let's bindings are first named as variables of their
// own, each defined by its equation (so a binding nothing relevant reads is dropped too). Every clause of the weakened
// system holds wherever the original's does, so a model of it is one of the original (no lifting needed); and a
// derivation of it is one of the original's once the dropped values are made again by the original clauses, which the
// original rule's replay does (`expand` reads each original clause's own free variables, which the weakened clause
// keeps by name). The predicates and their arguments stay as they are.
const varsOf = (s: Sx, out = new Set<string>(), shadow = new Set<string>()): Set<string> => {
  if (typeof s === 'string') { if (!shadow.has(s)) out.add(s); return out }
  if (s[0] === 'let') { const inner = new Set(shadow); for (const b of s[1] as Sx[][]) { varsOf(b[1]!, out, shadow); inner.add(b[0] as string) } return varsOf(s[2]!, out, inner) }
  for (const x of s.slice(1)) varsOf(x, out, shadow)
  return out
}
const boolOps = new Set(['and', 'or', 'not', '=>', '=', 'distinct', '<', '<=', '>', '>=', 'xor', 'true', 'false'])
const sortIn = (s: Sx, vars: Map<string, Sort>): Sort => (typeof s === 'string' ? (s === 'true' || s === 'false' ? 'Bool' : vars.get(s) ?? 'Int') : s[0] === 'ite' ? sortIn(s[2]!, vars) : s[0] === 'let' ? 'Int' : boolOps.has(s[0] as string) ? 'Bool' : 'Int')
export function slice(chc: Chc): {chc: Chc, dropped: number} {
  let fresh = 0, dropped = 0
  const clauses = chc.clauses.map(c0 => {
    const vars = new Map(c0.vars), conj: Sx[] = []
    // each let's bindings named apart (the name's sort its expression's) and defined by an equation of their own
    const open = (s: Sx, ren: Map<string, string>): Sx => {
      if (typeof s === 'string') return ren.get(s) ?? s
      if (s[0] !== 'let') return s.map((x, i) => (i === 0 ? x : open(x, ren)))
      const inner = new Map(ren)
      for (const b of s[1] as Sx[][]) {
        const n = `${b[0] as string}@s${fresh++}`, e = open(b[1]!, ren)
        vars.set(n, sortIn(e, vars)); conj.push(['=', n, e]); inner.set(b[0] as string, n)
      }
      return open(s[2]!, inner)
    }
    const flat = (s: Sx) => { if (Array.isArray(s) && s[0] === 'and') s.slice(1).forEach(flat); else if (s !== 'true') conj.push(s) }
    for (const s of c0.constraint) flat(open(s, new Map()))
    return {c0, vars, conj}
  })
  // Definitions and guards: x = e defines x where nothing else of the clause reads x (no other conjunct, no body
  // argument; the head may), and e doesn't.
  const plans = clauses.map(({c0, conj}) => {
    const body = new Set(c0.body.flatMap(a => a.args.flatMap(x => [...varsOf(x)]))), count = new Map<string, number>()
    for (const k of conj) for (const v of varsOf(k)) count.set(v, (count.get(v) ?? 0) + 1)
    const defs = new Map<string, number>()
    conj.forEach((k, i) => {
      if (!Array.isArray(k) || k[0] !== '=' || k.length !== 3) return
      for (const [x, e] of [[k[1]!, k[2]!], [k[2]!, k[1]!]] as const) if (typeof x === 'string' && !defs.has(x) && ![...defs.values()].includes(i) && !body.has(x) && count.get(x) === 1 && !varsOf(e).has(x)) defs.set(x, i)
    })
    return {defs, isDef: new Set(defs.values())}
  })
  const rel = new Map([...chc.preds].map(([p, ss]) => [p, ss.map(() => false)])), relVars = clauses.map(() => new Set<string>())
  for (let changed = true; changed;) {
    changed = false
    clauses.forEach(({c0, conj}, i) => {
      const mark = (v: string) => { if (!relVars[i]!.has(v)) { relVars[i]!.add(v); changed = true } }
      conj.forEach((k, j) => { if (!plans[i]!.isDef.has(j)) for (const v of varsOf(k)) mark(v) })
      c0.head?.args.forEach((h, j) => { if (rel.get(c0.head!.pred)![j]) for (const v of varsOf(h)) mark(v) })
      for (const v of [...relVars[i]!]) { const j = plans[i]!.defs.get(v); if (j !== undefined) for (const w of varsOf(conj[j]!)) mark(w) }
      for (const a of c0.body) a.args.forEach((x, j) => { if (!rel.get(a.pred)![j] && (typeof x !== 'string' || relVars[i]!.has(x))) { rel.get(a.pred)![j] = true; changed = true } })
    })
  }
  const out = clauses.map(({c0, vars, conj}, i): Clause => {
    const keep = conj.filter((_, j) => !plans[i]!.isDef.has(j) || [...plans[i]!.defs].some(([v, k]) => k === j && relVars[i]!.has(v)))
    dropped += conj.length - keep.length
    return used({vars, body: c0.body, constraint: keep, head: c0.head})
  })
  return {chc: {preds: chc.preds, clauses: out}, dropped}
}

// --- reading answers back on the original system ----------------------------------------------------------------------

// A derivation of the composed system (its rule's steps) as requests of the original rule: each composed step's
// variables valued (translate.ts's envOf), and each original clause it is made of given the values its own free
// variables have there. The caller replays them on the original rule (stepsOf) and checks the run against the original
// CHC (checkDerivation), as any run.
export function expand(bo: Built, bc: Built, cc: Composed, steps: Step[]): Raw[] | string {
  const raws: Raw[] = []
  for (const [n, s] of steps.entries()) {
    const env = envOf(bc.plans[s.clause]!, s)
    if (!env) return `composed step ${n}: definitions that never resolve`
    for (const part of cc.parts[s.clause]!) {
      const p = bo.plans[part.clause]!, raw: Raw = {c: bo.clauseNames[part.clause]!}
      for (let k = 0; k < bo.inInt; k++) raw[`x${k}`] = 0
      for (let k = 0; k < bo.inBool; k++) raw[`y${k}`] = false
      for (const [v, bd] of p.bound) {
        if (bd.kind !== 'input') continue
        // (a variable the composed clause doesn't read, any value)
        const x = env.get(part.ren.get(v) ?? v) ?? (bd.sort === 'Int' ? 0n : false)
        raw[`${bd.sort === 'Int' ? 'x' : 'y'}${bd.k}`] = typeof x === 'bigint' ? Number(x) : x
      }
      raws.push(raw)
    }
  }
  return raws
}

// An invariant of the composed rule (`inv`, over its state: the location and the slots, the original's names) as laws
// of the original rule. At a location the composition kept (and at the start), `inv` itself. At an eliminated
// predicate Q, taken in the reverse order of elimination: the clauses into Q and out of Q when it was eliminated join
// predicates that were alive then, each kept or eliminated after Q, so each already has its condition J; their products
// are clauses of the system after Q was gone, which J models, so no state J allows at a predecessor reaches, through Q,
// a state J doesn't allow at a successor. That two-step goal (the rule of those clauses alone), refuted by the kernel's
// search, colored at the state after the first step, gives an interpolant I over Q's state: every state the clauses
// into Q make from J is in I, and from I every clause out of Q keeps J. J with `loc = Q → I` models the clauses before Q
// was eliminated; in the end, every original clause. Nothing here is trusted: the caller proves the laws (and the law
// that error is never reached) of the original rule with the kernel.
// (`fns`, `facts`: the original rule's functions, a remainder by a constant say, which an invariant may read where the
// clauses of one predicate don't)
export function lift(cc: Composed, inv: C, budget: {until: number, wall?: number}, fns: Pick<Machine, 'fns' | 'facts'> = {}): {laws: Law[]} | {why: string} {
  const preds = [...cc.chc.preds.keys()], loc: E = {op: 'var', name: 'loc'}
  const at = (p: string): C => ({op: '=', a: loc, b: {op: 'const', value: 1 + preds.indexOf(p)}})
  const implies = (a: C, b: C): C => ({op: 'or', xs: [{op: 'not', x: a}, b]})
  // (each condition read at its location: the location put in, the rest folded)
  const atLoc = (c: C, p: string | 0): C => simpC(substC(c, {vars: {loc: {op: 'const', value: p === 0 ? 0 : 1 + preds.indexOf(p)}}, maps: {}, flags: {}}))
  const kept = preds.filter(p => !cc.eliminated.includes(p) && cc.chc.clauses.some(c => c.head?.pred === p || c.body[0]?.pred === p))
  const laws: Law[] = [{name: 'never error', holds: {op: 'not', x: {op: '=', a: loc, b: {op: 'const', value: 1 + preds.length}}}}, {name: 'the composed invariant at the start', holds: implies({op: '=', a: loc, b: {op: 'const', value: 0}}, atLoc(inv, 0))},
    ...kept.map(p => ({name: `the composed invariant at ${p}`, holds: implies(at(p), atLoc(inv, p))}))]
  for (const st of [...cc.steps].reverse()) {
    const J: C = {op: 'and', xs: laws.map(l => l.holds)}
    const bt = build({preds: cc.chc.preds, clauses: [...st.into, ...st.out]}, 'a predicate eliminated'), m0 = bt.rule.machine
    const m: Machine = {...m0, fns: {...fns.fns, ...m0.fns}, facts: [...(fns.facts ?? []).filter(f => !m0.facts?.some(g => g.name === f.name)), ...(m0.facts ?? [])]}
    const primed = {vars: Object.fromEntries(Object.keys(m.state).map(n => [n, {op: 'var', name: `${n}'`} as E])), maps: {}, flags: {}}
    const when: C = {op: 'and', xs: [J, {op: 'not', x: at(st.pred)}, ...bt.rule.kindLaws().map(l => l.holds)]}
    // (the kernel's step-law goal reads no function: an invariant that reads one, a remainder say, goes to the precondition)
    let out: ReturnType<typeof cutInterpolant>
    try { out = cutInterpolant(m, when, substC(J, primed), 2, budget, true) } catch (e) { out = {unknown: (e as Error).message.slice(0, 80)} }
    // Where no interpolant comes and no clause out of Q leaves a value to the request: the weakest precondition itself,
    // each clause's head put into J where the clause fires.
    if (!('itp' in out) && !('sat' in out)) {
      const pre = wp(bt, m, st.into.length, J)
      if (pre) { laws.push({name: `at ${st.pred}`, holds: implies(at(st.pred), atLoc(pre, st.pred))}); continue }
    }
    if (!('itp' in out)) return {why: `${st.pred}: ${'sat' in out ? 'a model (the invariant is not inductive here)' : out.unknown}`}
    const back = {vars: Object.fromEntries(Object.keys(m.state).map(n => [`${n}~1`, {op: 'var', name: n} as E])), maps: {}, flags: {}}
    laws.push({name: `at ${st.pred}`, holds: implies(at(st.pred), atLoc(substC(out.itp, back), st.pred))})
  }
  return {laws}
}

// J after each clause from `first` on, where it fires (undefined where one leaves a value to the request).
function wp(bt: Built, m: Machine, first: number, J: C): C | undefined {
  const parts: C[] = []
  for (let j = first; j < bt.plans.length; j++) {
    if ([...bt.plans[j]!.bound.values()].some(x => x.kind === 'input')) return undefined
    const sub = {vars: {c: {op: 'const', value: j} as E}, maps: {}, flags: {}}
    const after = {vars: Object.fromEntries(Object.keys(m.state).map(n => [n, simpE(substE(m.step.state?.[n] ?? {op: 'var', name: n}, sub))])), maps: {}, flags: {}}
    parts.push({op: 'or', xs: [{op: 'not', x: simpC(substC(bt.fires[j]!, sub))}, simpC(substC(J, after))]})
  }
  return simpC({op: 'and', xs: parts})
}
// A sat answer of the composed rule, its invariant `inv`, as the original rule's: lifted (above), then the original
// law proven by the kernel with the lifted laws beside it (proveRule, no search), all by `wall`.
export function liftProven(cc: Composed, bo: Built, inv: C, wall: number): {proven: boolean, why?: string, laws?: number, liftMs: number, proveMs: number} {
  const t0 = performance.now(), mo = bo.rule.machine
  let l: ReturnType<typeof lift>
  const ar = arithmetic(divisorsIn([inv]))
  try { l = withDeadline(wall, () => lift(cc, inv, {until: wall, wall}, {fns: {...ar.fns, ...mo.fns}, facts: [...ar.facts.filter(f => !mo.facts?.some(g => g.name === f.name)), ...(mo.facts ?? [])]})) } catch (e) { l = {why: (e as Error).message} }
  const t1 = performance.now()
  if ('why' in l) return {proven: false, why: `not lifted: ${l.why}`.slice(0, 160), liftMs: Math.round(t1 - t0), proveMs: 0}
  const v = withDeadline(wall, () => proveRule(bo.rule, [bo.law, {name: 'lifted', holds: {op: 'and', xs: l.laws.map(x => x.holds)}}], {search: false})), ms = {liftMs: Math.round(t1 - t0), proveMs: Math.round(performance.now() - t1), laws: l.laws.length}
  return v.proven && v.checked ? {proven: true, ...ms} : {proven: false, why: `the original's proof: ${v.goal ?? ''} ${v.stuck ?? ''}`.slice(0, 160), ...ms}
}
// The laws of a sat answer of the composed rule as one condition (undefined where one reads a key or "there exists",
// which the lifting doesn't read).
export const invOf = (laws: Law[]): C | undefined => (laws.every(l => !l.forall && !l.keys?.length && !l.some?.length) ? {op: 'and', xs: laws.map(l => l.holds)} : undefined)

// The system the searches read: the original weakened by its cone of influence (`slice`) and its chains composed away
// (`chains`), or undefined where neither changes it.
export function prepare(chc: Chc, opts: {slice?: boolean, chains?: boolean}): Composed | undefined {
  const s = opts.slice ? slice(chc) : {chc, dropped: 0}
  if (!opts.chains) return s.dropped ? {chc: s.chc, parts: s.chc.clauses.map((c, i) => [{clause: i, ren: new Map([...c.vars.keys()].map(v => [v, v]))}]), eliminated: [], steps: []} : undefined
  const cc = compose(s.chc)
  return cc.eliminated.length || s.dropped ? cc : undefined
}
