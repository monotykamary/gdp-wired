// Search-only proposals. The existing step checker proves all the proposed state
// invariants and the original step law, or this stage contributes nothing.
import {type C, type E, type Law, type Machine, hasFinite} from './machine.ts'
import {checkWorkEndpoint} from './wall.ts'
import {type Instances, type StepLaw, type Tree, checkStepLaws, obligations, stepLawObligations} from '../kernel/kernel.ts'
import {grow, proveStepLaws} from '../kernel/prove.ts'
import {kindConjuncts, sparseKindProof} from './sparse-kind-proof.ts'

type Tagged<T, O> = T extends {op: infer K} ? O extends K ? T & {op: O} : never : never
type Ast<O> = Tagged<C | E, O>
const repr = (x: unknown) => JSON.stringify(x)
const same = (a: unknown, b: unknown): boolean => repr(a) === repr(b)
const v = (name: string): Ast<'var'> => ({op:'var', name})
const n = (value: number): Ast<'const'> => ({op:'const', value})
const get = (map: string, key: E): Ast<'get'> => ({op:'get', map, key})
const eq = (a: E, b: E): Ast<'='> => ({op:'=', a, b})
const le = (a: E, b: E): C => ({op:'<=', a, b})
const neg = (x: C): Ast<'not'> => ({op:'not', x})
const imp = (a: C, b: C): C => ({op:'or', xs:[neg(a), b]})

// Bound the syntax walk even on hand-built machines with shared subterms. Abort
// rather than interpreting a partial walk as evidence that no other write exists.
class TooWide extends Error {}
function objects(t: unknown): Record<string, unknown>[] {
  const seen = new Set<object>(), out: Record<string, unknown>[] = [], stack = [t]
  while (stack.length) {
    const x = stack.pop()
    if (!x || typeof x !== 'object' || seen.has(x)) continue
    if ((seen.size & 255) === 0) checkWorkEndpoint('step seed syntax')
    if (seen.size >= 8192) throw new TooWide()
    seen.add(x)
    if (!Array.isArray(x)) out.push(x as Record<string, unknown>)
    const xs = Object.values(x)
    for (let i = xs.length - 1; i >= 0; i--) stack.push(xs[i])
  }
  return out
}
const nodes = <O extends (C | E)['op']>(t: unknown, op: O): Ast<O>[] =>
  objects(t).filter(x => x.op === op) as unknown as Ast<O>[]
const values = (t: E, depth = 0): E[] => {
  if (depth > 16) throw new TooWide()
  return t.op === 'if' ? [...values(t.then, depth + 1), ...values(t.else, depth + 1)] : [t]
}
function flagClosure(m: Machine, t: unknown): unknown[] {
  const roots = [t], seen = new Set<string>()
  for (let i = 0; i < roots.length; i++) for (const f of nodes(roots[i], 'flag')) {
    const c = m.step.flags?.[f.name]
    if (c && !seen.has(f.name)) { seen.add(f.name); roots.push(c) }
    if (roots.length > 64) throw new TooWide()
  }
  return roots
}
function conjuncts(m: Machine, c: C, active = new Set<string>(), depth = 0): C[] {
  if (depth > 16) throw new TooWide()
  if (c.op === 'and') return c.xs.flatMap(x => conjuncts(m, x, active, depth + 1))
  if (c.op === 'flag' && !active.has(c.name) && m.step.flags?.[c.name])
    return conjuncts(m, m.step.flags[c.name]!, new Set([...active,c.name]), depth + 1)
  return [c]
}
function seed(holds: C, name: string, forall?: string): Law {
  return {name:`step seed: ${name}`, holds, ...(forall === undefined ? {} : {forall})}
}

// Find the access guards for the exact fields the step law expects to stay
// unchanged (or only change in one direction). An old-state tag on one field
// can make a default-valued allocation guard on a sibling field impossible.
function compatible(m: Machine, sl: StepLaw): Law[][] {
  if (!sl.forall || sl.keys?.length || sl.then.op !== 'or' || !m.maps) return []
  const ante = sl.then.xs.find(x => x.op === 'not')?.x, k = v(sl.forall)
  if (!ante || nodes(ante, 'var').some(x => x.name !== k.name)) return []
  const getters = nodes(ante, 'get'), maps = [...new Set(getters.map(x => x.map))], old = maps[0]
  if (!old || maps.length !== 1 || !(old in m.maps) || !getters.every(x => same(x.key,k))) return []
  const changed = [...new Set(nodes(sl.then, 'get').filter(x => x.map.endsWith("'")).map(x => x.map.slice(0,-1)))]
  const kept = new Map<string,C>()
  for (const name of changed) {
    const w = m.step.maps?.[name]
    if (!w) continue
    // Try the negation of actual default tests, and likewise the complement of
    // a negated Boolean test on a zero-default cell. Merely occurring in a guard
    // does not make the proposal true; it just gives the prover a useful guess.
    for (const o of objects(flagClosure(m, w.value))) {
      if (o.op !== '=' && o.op !== 'not') continue
      const inverted = o.op === 'not', c = (inverted ? o.x : o) as C
      if (c.op !== '=') continue
      const [a,b] = c.a.op === 'get' ? [c.a,c.b] : [c.b,c.a]
      if (a.op !== 'get' || b.op !== 'const' || a.map === old || kept.has(a.map)) continue
      if (inverted ? !(m.maps[a.map] === 0 && b.value === 1) : m.maps[a.map] !== b.value) continue
      const test=eq(get(a.map,k),b)
      kept.set(a.map,inverted ? test : neg(test))
    }
  }
  const dot = old.lastIndexOf('.'), prefix = dot === -1 ? undefined : old.slice(0,dot+1)
  const local = (x: string) => Number(prefix !== undefined && x.startsWith(prefix))
  return [...kept].sort(([a],[b]) => local(b)-local(a)).slice(0,4)
    .map(([a,test]) => [seed(imp(ante,test),`${old} excludes the allocation test for ${a}`,k.name)])
}

// Derive a cursor anchor from an actual equality guard and corresponding writes
// of both the old and successor cursor. Match copied values by exact expression,
// not by names or adjacency in the user's source.
function coherence(m: Machine, sl: StepLaw): Law[][] {
  const state = m.step.state, maps = m.step.maps, defaults = m.maps
  if (sl.forall || !maps || !state || !defaults || !sl.when) return []
  const inputs = new Set(m.inputs), vars = Object.keys(state)
  const used = new Set([...m.inputs, ...m.params, ...Object.keys(m.state), ...nodes(m,'var').map(x => x.name)])
  const key = ['$','$$','$$$'].find(x => !used.has(x))
  if (!key) return []
  const k = v(key)
  const mvs = Object.fromEntries(Object.entries(maps).map(([a,w])=>[a,values(w.value)]))
  const svs = Object.fromEntries(Object.entries(state).map(([a,e])=>[a,values(e)]))
  const gvars = new Set(nodes([sl.then,sl.when],'var').map(x=>x.name.replace(/'$/,'')))
  const clocks = new Map<string,E>()
  for (const {a,b} of nodes(m.assume,'<=')) {
    if (a.op !== 'var' || b.op !== 'var' || !inputs.has(b.name)) continue
    const e = state[a.name]
    if (e?.op === 'max' && ((same(e.a,a)&&same(e.b,b)) || (same(e.b,a)&&same(e.a,b)))) clocks.set(b.name,a)
  }
  // Normalize a guard to the stored observation and clock. It is a proposal,
  // not an equivalence asserted between the original and normalized guards.
  function relation(c: C, acting: Ast<'var'>): {f: C, clock: boolean} | undefined {
    let clock = false
    function rewrite(x: unknown, depth = 0): unknown {
      if (depth > 32) throw new TooWide()
      if (!x || typeof x !== 'object') return x
      if (Array.isArray(x)) return x.map(z=>rewrite(z,depth+1))
      const a = x as Record<string,unknown>
      if (a.op === 'if') {
        const e = a.else as E
        if (e.op === 'get' && same(e.key,acting)) return get(e.map,k)
      }
      if (a.op === 'var') {
        const s = a.name as string
        if (s === acting.name) return k
        if (clocks.has(s)) {clock = true; return clocks.get(s)}
      }
      return Object.fromEntries(Object.entries(a).map(([k,z])=>[k,rewrite(z,depth+1)]))
    }
    const f = rewrite(c) as C
    if (nodes(f,'var').some(x=>x.name!==key&&!vars.includes(x.name)&&!m.params.includes(x.name)) ||
      nodes(f,'get').some(x=>!(x.map in defaults!)||!same(x.key,k)) ||
      objects(f).some(x=>x.op==='if'||x.op==='all'||x.op==='flag')) return
    return {f,clock}
  }
  for (const test of nodes(flagClosure(m,sl.when),'=')) {
    const [cur,cell] = test.a.op === 'get' ? [test.b,test.a] : [test.a,test.b]
    if (cur.op !== 'var' || cell.op !== 'get' || cell.key.op !== 'var' || !inputs.has(cell.key.name)) continue
    const act = cell.key, primary = cell.map
    const next = svs[cur.name]?.find(e=>e.op==='add'&&same(e.a,cur)&&same(e.b,n(1)))
    if (!next || !mvs[primary]?.some(e=>same(e,next)) || !mvs[primary].some(e=>same(e,cur))) continue
    const seen = new Set<string>(), out: Law[] = []
    const push = (f: C, label: string, keyed = true) => {
      const j=repr(f); if(seen.has(j)) return
      seen.add(j); out.push(seed(f,`${label} [${out.length}]`,keyed ? key : undefined))
    }
    const match = eq(get(primary,k),cur)
    const secondary = Object.keys(mvs).filter(x=>x!==primary && mvs[x]!.some(e=>same(e,cur)) && !mvs[x]!.some(e=>same(e,next)))
    push(le(get(primary,k),cur),`${primary} is at most the cursor`)
    for (const x of secondary) push(le(get(x,k),get(primary,k)),`${x} is at most ${primary}`)
    const identity = new Set<string>()
    let copies = 0
    for (const s of vars.filter(x=>gvars.has(x)&&x!==cur.name)) for (const mp of Object.keys(mvs)) {
      if (mp === primary || secondary.includes(mp)) continue
      const both = svs[s]!.filter(e=>e.op!=='const'&&!same(e,v(s))&&mvs[mp]!.some(t=>same(t,e)))
      if (!both.length) continue
      const now = both.find(e=>e.op==='var'&&clocks.has(e.name))
      if (now?.op === 'var') push(le(v(s),clocks.get(now.name)!),`${s} is not past the clock`,false)
      push(imp(match,now ? le(v(s),get(mp,k)) : eq(get(mp,k),v(s))),`${mp} is current on a matched cursor`)
      copies++
      if (both.some(e=>same(e,act))) identity.add(mp)
    }
    if (!copies) continue
    const timeGoal = nodes(sl.then,'var').some(x=>clocks.has(x.name)), post = nodes(sl.then,'var').some(x=>x.name.endsWith("'"))
    const readers = new Set(nodes(flagClosure(m,[sl.when,...vars.filter(x=>gvars.has(x)).map(x=>state[x])]),'get').map(x=>x.map))
    for (const [mp,wr] of Object.entries(maps)) {
      if (!readers.has(mp) || mp===primary || secondary.includes(mp) || identity.has(mp)) continue
      const b = get(mp,k), def = defaults[mp]
      if (def === undefined) continue
      const arms: {tag: number, path: C[]}[] = []
      const visit = (e: E, path: C[]): void => {
        if (path.length > 16 || arms.length > 6) throw new TooWide()
        if (e.op==='if') {visit(e.then,[...path,e.c]);visit(e.else,[...path,neg(e.c)])}
        else if (e.op==='const' && e.value!==def) arms.push({tag:e.value,path})
      }
      visit(wr.value,[])
      for (const {tag,path} of arms) {
        const cs = flagClosure(m,path)
        if (timeGoal) {
          for (const c of nodes(cs,'not').filter(x=>x.x.op==='and')) {
            const r = relation(c,act)
            if (r?.clock && nodes(r.f,'get').some(x=>identity.has(x.map)))
              push(imp(neg(eq(b,n(def))),r.f),`${mp} retains its clock guard`)
          }
        } else if (post) {
          const top = path.flatMap(c=>conjuncts(m,c))
          for (const c of nodes(cs,'=')) {
            const r = relation(c,act)
            if (r?.f.op!=='=' || !nodes(r.f,'get').some(x=>identity.has(x.map)) || ![r.f.a,r.f.b].some(z=>same(z,k))) continue
            push(imp(eq(b,n(tag)),top.some(x=>same(x,c)) ? r.f : neg(r.f)),`${mp} retains the identity test for ${tag}`)
          }
        }
      }
    }
    if (out.length <= 16) return [out]
  }
  return []
}

export function stepSeedFamilies(m: Machine, sl: StepLaw): Law[][] {
  try {
    if ((sl.steps ?? 1) !== 1 || m.history || m.sums || m.counts || !m.maps || m.primitiveFailure || m.inputMaps?.length ||
        objects([m,sl]).some(x=>x.finite !== undefined) || hasFinite(sl)) return []
    return sl.forall ? compatible(m,sl) : coherence(m,sl)
  } catch (error) {
    if (error instanceof TooWide) return []
    throw error
  }
}

// Only trust the resulting ordinary proof. Kind reminders can be omitted for
// an allocation-guard proposal: proving with fewer hypotheses is stronger and
// avoids instantiating unrelated record fields at all possible write keys.
function atKeyProof(m: Machine, family: Law[], sl: StepLaw): ReturnType<typeof proveStepLaws> | undefined {
  // Every supplied hypothesis is still required at initiation and preservation.
  // Start with the observed key only; instantiation is a proof-search choice.
  const [law] = family, key = sl.forall!
  const inst = {[law!.name]: [v(key)]}, inv: Record<string, Instances> = {[law!.name]:{[law!.name]:[v(`${key}#`)]}}
  const lt: Record<string,Tree> = {}, st: Record<string,Tree> = {}
  let count = 0
  for (const [goals, dst] of [[obligations(m,family,inv),lt],[stepLawObligations(m,family,inst,sl),st]] as const) {
    for (const g of goals) {
      const r = grow(g)
      if (!('tree' in r)) return {proven:false,checked:false,nodes:count,leaves:0,failed:{goal:g.name,stuck:r.stuck,why:r.why,witness:r.witness}}
      count += r.nodes
      dst[g.name] = r.tree
    }
  }
  const proof = {laws:{instances:inv,trees:lt},instances:inst,trees:st}
  if (!checkStepLaws(m,family,[sl],proof)) return undefined
  return {proven:true,checked:true,proof,nodes:count,leaves:0}
}
export function tryStepSeed(m: Machine, laws: Law[], kinds: Law[], sl: StepLaw, seeds: Law[], sparse = true) {
  const extraKinds = kinds.filter(k => !laws.some(l => l.name === k.name))
  const given = [...extraKinds, ...laws]
  if (!seeds.length || new Set(seeds.map(s => s.name)).size !== seeds.length || seeds.some(s => given.some(l => l.name === s.name))) return undefined
  const atKey = !laws.length && seeds.length === 1 && sl.forall && seeds[0]!.forall === sl.forall && !m.facts?.length &&
    !Object.values(m.step.flags ?? {}).some(c => c.op === 'all')
  if (atKey && sparse) {
    const checked = atKeyProof(m, seeds, sl)
    if (!checked?.proof || !checked.proven || !checked.checked) return undefined
    // Kind laws are independent obligations of the public call, not optional
    // conclusions. Check them separately to keep the sparse step proof small.
    if (!extraKinds.length) return {family: seeds, checked}
    const kindLaws = kindConjuncts(extraKinds, seeds), proof = sparseKindProof(m, kindLaws, Infinity)
    return proof ? {family: seeds, checked, kindProof: {laws: kindLaws, proof}} : undefined
  }
  const family = [...given, ...seeds], checked = proveStepLaws(m, family, [sl])
  if (!checked.proof || !checked.proven || !checked.checked || !checkStepLaws(m, family, [sl], checked.proof)) return undefined
  return {family, checked}
}
