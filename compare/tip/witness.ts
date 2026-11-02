// Untrusted existential witness proposals. A first matching position in any
// list-shaped datatype, in Int or a Peano index type. Nothing here asserts that
// the position works: translate.ts substitutes the term in the original goal,
// then the ordinary datatype prover must prove that stronger statement.
import {type Sx, type Tip, type Ty, sameTy, substTy, tyOf} from './tip.ts'

// Simultaneous, capture-avoiding substitution. A witness may mention outer
// variables shadowed by a let/match/lambda inside the existential's body.
export function substituteWitnesses(s: Sx, by: Map<string, Sx>): Sx {
  const tokens = (t: Sx, out: Set<string>): void => { if (typeof t === 'string') out.add(t); else t.forEach(x => tokens(x, out)) }
  const taken = new Set<string>(), free = new Set<string>()
  tokens(s, taken)
  for (const t of by.values()) { tokens(t, taken); tokens(t, free) }
  let seq = 0
  const bind = (names: string[], env: Map<string, Sx>): {names: string[], env: Map<string, Sx>} => {
    const next = new Map(env)
    return {names: names.map(n => {
      next.delete(n)
      if (!free.has(n)) return n
      let fresh: string
      do { fresh = `$witnessBound${seq++}` } while (taken.has(fresh))
      taken.add(fresh); next.set(n, fresh); return fresh
    }), env: next}
  }
  const go = (t: Sx, env: Map<string, Sx>): Sx => {
    if (typeof t === 'string') return env.get(t) ?? t
    if (['forall', 'exists', 'lambda', 'let'].includes(t[0] as string)) {
      const bs = t[1] as Sx[][], b = bind(bs.map(x => x[0] as string), env)
      return [t[0]!, bs.map((x, i) => [b.names[i]!, t[0] === 'let' ? go(x[1]!, env) : x[1]!]), go(t[2]!, b.env)]
    }
    if (t[0] === 'match') return ['match', go(t[1]!, env), (t[2] as Sx[][]).map(c => {
      if (!Array.isArray(c[0])) return [c[0]!, go(c[1]!, env)]
      const b = bind(c[0].slice(1) as string[], env)
      return [[c[0][0]!, ...b.names], go(c[1]!, b.env)]
    })]
    if (t[0] === '_' || t[0] === 'as') return [t[0], go(t[1]!, env), ...t.slice(2)]
    return t.map(x => go(x, env))
  }
  return go(s, by)
}

export function indexWitnesses(tip: Tip, index: Sx, outer: {name: string, ty: Sx}[]): Sx[] {
  const tvars = new Set(tip.goal.params), it = tyOf(index, tvars)
  if (it.k !== 'con' || it.args.length) return []
  const id = tip.datas.get(it.name)
  const zero = id?.ctors.find(c => !c.fields.length)
  const succ = id?.ctors.find(c => c.fields.length === 1 && sameTy(c.fields[0]!.ty, it))
  const integer = it.name === 'Int'
  if (!integer && !(id && !id.params.length && id.ctors.length === 2 && zero && succ)) return []
  const out: Sx[] = []
  const taken = new Set([...tip.funs.keys(), ...tip.ctorOf.keys(), ...tip.selectorOf.keys(), ...tip.constDecls.keys(), ...outer.map(v => v.name)])
  const fresh = (stem: string): string => { let n = stem; while (taken.has(n)) n += '_'; taken.add(n); return n }
  for (const list of outer) {
    const lt = tyOf(list.ty, tvars)
    if (lt.k !== 'con') continue
    const d = tip.datas.get(lt.name)
    if (!d || d.ctors.length !== 2 || d.params.length !== lt.args.length) continue
    const nil = d.ctors.find(c => !c.fields.length), cons = d.ctors.find(c => c.fields.length === 2)
    if (!nil || !cons) continue
    const sub = new Map(d.params.map((p, i) => [p, lt.args[i]!]))
    const fields = cons.fields.map(f => substTy(f.ty, sub)), tail = fields.findIndex(t => sameTy(t, lt))
    if (tail < 0 || sameTy(fields[1 - tail]!, lt)) continue
    const elem = fields[1 - tail]!
    if (elem.k === 'fun') continue
    for (const item of outer.filter(v => sameTy(tyOf(v.ty, tvars), elem))) {
      if (out.length === 4) return out
      const name = fresh('$indexWitness'), x = fresh('$item'), xs = fresh('$list'), h = fresh('$head'), t = fresh('$tail')
      const used = new Set<string>()
      const vars = (ty: Ty): void => { if (ty.k === 'var') used.add(ty.name); else if (ty.k === 'con') ty.args.forEach(vars); else {ty.args.forEach(vars); vars(ty.ret)} }
      vars(lt); vars(elem)
      const params = tip.goal.params.filter(p => used.has(p))
      const z: Sx = integer ? '0' : zero!.name
      const rec: Sx = [name, x, t], next: Sx = integer ? ['+', '1', rec] : [succ!.name, rec]
      const body: Sx = ['match', xs, [[nil.name, z], [[cons.name, ...(tail === 0 ? [t, h] : [h, t])], ['ite', ['=', x, h], z, next]]]]
      tip.funs.set(name, {name, params, args: [{name: x, ty: elem}, {name: xs, ty: lt}], ret: it, body, group: [name]})
      out.push([...(params.length ? [['_', name, ...params] as Sx] : [name]), item.name, list.name])
    }
  }
  return out
}
