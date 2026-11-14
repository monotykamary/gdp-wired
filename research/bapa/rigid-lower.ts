// Experimental frontend lowering. Not wired into public proof acceptance/export.
// All generated facts remain ordinary, explicit assumptions of the old kernel.
import {argsKey, evalC, interpret, type C, type E, type Fn, type Law, type Machine, type Request, type State} from '../../core/machine.ts'
import {scope} from '../../kernel/kernel.ts'
import {type FunctionInstanceSpec} from '../../kernel/function-instances.ts'
import {assertValidatedRigidInstance, validateRigidInstance, type RigidSignature, type RigidTerm, type ValidatedRigidInstance} from './rigid-instance.ts'
const v = (name: string): E => ({op: 'var', name})
const k = (value: number): E => ({op: 'const', value})
const and = (xs: C[]): C => ({op: 'and', xs})
const implies = (a: C, b: C): C => ({op: 'or', xs: [{op: 'not', x: a}, b]})
const get = (map: string, args: E[]): E => ({op: 'get', map, key: argsKey(args)})
const freeze = <T>(x: T): T => {
  if (x && typeof x === 'object' && !Object.isFrozen(x)) { for (const y of Object.values(x)) freeze(y); Object.freeze(x) }
  return x
}
function tableFn(dimensions: number[], values: number[]): Fn {
  const arity = dimensions.length
  const call = `(...a) => { const d=${JSON.stringify(dimensions)}, v=${JSON.stringify(values)}; if(a.length!==d.length)throw Error('rigid function arity'); let i=0; for(let j=0;j<a.length;j++){if(!Number.isSafeInteger(a[j])||a[j]<0)throw Error('rigid function coordinate'); if(a[j]>=d[j])return 0; i=i*d[j]+a[j];} return v[i]; }`
  if (arity === 1) return {js: call}
  // The existing function representation's square pairing, not a new radix.
  const js = `(() => { const f=(${call}); return k => { if(!Number.isSafeInteger(k)||k<0)throw Error('rigid function key'); const a=[]; let z=k; for(let i=1;i<${arity};i++){let s=Math.floor(Math.sqrt(z));while(s*s>z)s--;while((s+1)*(s+1)<=z)s++;const b=z-s*s;a.unshift(b);z=s-b;}a.unshift(z);if(a.some(x=>x<0))return 0;return f(...a); }; })()`
  return {js, arity, call}
}
function materialize(dimensions: number[], read: (args: number[]) => number, checkpoint: () => void): Fn {
  const values: number[] = [], args: number[] = []
  const go = (i: number): void => {
    if (i === dimensions.length) { if ((values.length & 255) === 0) checkpoint(); values.push(read(args)); return }
    for (let n = 0; n < dimensions[i]!; n++) { args[i] = n; go(i + 1) }
  }
  go(0)
  return tableFn(dimensions, values)
}

export function lowerRigid(base: Machine, source: RigidSignature) {
  const signature = JSON.parse(JSON.stringify(source)) as RigidSignature
  // Empty domains check declaration/term sorts without requiring an inhabited instance.
  validateRigidInstance(signature, JSON.stringify({params: Object.fromEntries(Object.values(signature.sorts).map(p => [p, 0])), tables: Object.fromEntries(Object.keys(signature.symbols).map(s => [s, []]))}), () => {})
  const m = structuredClone(base), facts: Law[] = [...(m.facts ?? [])], fns: Record<string, Fn> = {...m.fns}
  const taken = new Set([...m.params, ...m.inputs, ...Object.keys(m.state), ...Object.keys(m.maps ?? {}), ...(m.inputMaps ?? []), ...Object.keys(fns), ...Object.keys(m.counts ?? {}), ...Object.keys(m.step.flags ?? {}), ...facts.map(l => l.name)])
  const fresh = (hint: string): string => { let name = hint, n = 2; while (taken.has(name)) name = `${hint}${n++}`; taken.add(name); return name }
  for (const parameter of Object.values(signature.sorts)) if (!m.params.includes(parameter)) throw Error(`rigid sort size ${parameter} is not an immutable parameter`)
  const bound = (sort: string): E => {
    const name = signature.sorts[sort]; if (!name) throw Error(`unknown rigid sort ${sort}`)
    return v(name)
  }
  const domain = (sorts: readonly string[], args: E[]): C => and(sorts.map((sort, i) => ({op: '<', a: args[i]!, b: bound(sort)})))
  const abstractFn = (arity: number): Fn => ({js: "() => { throw Error('rigid instance not bound'); }", ...(arity > 1 ? {arity, call: "() => { throw Error('rigid instance not bound'); }"} : {})})
  const range = (symbol: string, sorts: readonly string[], result?: string) => {
    const keys = sorts.map((_, i) => fresh(`rigid_${symbol}_arg${i}`)), args = keys.map(v), value = get(symbol, args)
    const holds: C = result ? {op: '<', a: value, b: bound(result)} : {op: '<=', a: value, b: k(1)}
    facts.push({name: fresh(`rigid_${symbol}_range`), forall: keys[0]!, ...(keys.length > 1 ? {keys: keys.slice(1)} : {}), holds: implies(domain(sorts, args), holds)})
  }
  for (const [symbol, decl] of Object.entries(signature.symbols)) {
    if (taken.has(symbol) || !decl.args.length) throw Error(`rigid symbol collision or zero arity: ${symbol}`)
    taken.add(symbol); fns[symbol] = abstractFn(decl.args.length); range(symbol, decl.args, decl.result)
  }
  const auxiliaries: Record<string, string> = Object.create(null)
  for (const ax of signature.axioms) {
    if (ax.forall.length !== 2) throw Error('rigid lowering supports two universal binders')
    const symbol = fresh(`rigid_${ax.name}_choice`), keys = ax.forall.map((_, i) => fresh(`rigid_${ax.name}_key${i}`)), args = keys.map(v)
    auxiliaries[ax.name] = symbol; fns[symbol] = abstractFn(2)
    const env: Record<string, E> = Object.fromEntries(ax.forall.map((b, i) => [b.name, args[i]!]))
    env[ax.exists.name] = get(symbol, args)
    const term = (t: RigidTerm): E => {
      if ('variable' in t) { if (!env[t.variable]) throw Error('unbound rigid axiom variable'); return env[t.variable]! }
      const d = signature.symbols[t.call]; if (!d || d.result === undefined || d.args.length !== t.args.length) throw Error('invalid rigid function term')
      return get(t.call, t.args.map(term))
    }
    const body: C[] = [{op: '<', a: env[ax.exists.name]!, b: bound(ax.exists.sort)}]
    for (const atom of ax.body) {
      const d = signature.symbols[atom.relation]; if (!d || d.result !== undefined || d.args.length !== atom.args.length) throw Error('invalid rigid relation atom')
      body.push({op: '=', a: get(atom.relation, atom.args.map(term)), b: k(1)})
    }
    const holds = implies(domain(ax.forall.map(b => b.sort), args), and(body)), name = fresh(`rigid_${ax.name}_axiom`)
    facts.push({name, forall: keys[0]!, keys: [keys[1]!], holds})
  }
  m.fns = fns; m.facts = facts; scope(m)
  const schemaText = JSON.stringify(signature)
  const bind = (instance: ValidatedRigidInstance, otherParams: Readonly<Record<string, number>> = {}, checkpoint: () => void = () => {}) => {
    assertValidatedRigidInstance(instance)
    if (instance.schemaText !== schemaText) throw Error('rigid instance belongs to a different precondition')
    const out = structuredClone(m)
    for (const [symbol, decl] of Object.entries(signature.symbols)) {
      const dimensions = decl.args.map(sort => instance.params[signature.sorts[sort]!]!)
      out.fns![symbol] = materialize(dimensions, args => instance.read(symbol, args), checkpoint)
    }
    for (const ax of signature.axioms) {
      const dimensions = ax.forall.map(b => instance.params[signature.sorts[b.sort]!]!)
      out.fns![auxiliaries[ax.name]!] = materialize(dimensions, args => instance.witness(ax.name, args), checkpoint)
    }
    // These equalities document this concrete machine's precondition only.
    // Generic interpret.init does NOT enforce pre. The runtime below instead
    // closes over immutable parameters and exposes no per-step rebinding.
    // abstractMachine retains symbolic sizes for the source theorem.
    out.pre = and([...(out.pre ? [out.pre] : []), ...Object.entries(instance.params).map(([name, value]): C => ({op: '=', a: v(name), b: k(value)}))])
    scope(out)
    const machine = freeze(out), params = Object.freeze({...otherParams, ...instance.params})
    for (const [name, value] of Object.entries(instance.params)) if (otherParams[name] !== undefined && otherParams[name] !== value) throw Error('cannot rebind a rigid instance parameter')
    if (machine.pre && !evalC(machine.pre, params, {scalars: {}, maps: {}}, machine)) throw Error('bound parameters violate the source precondition')
    const runtime = interpret(machine, checkpoint)
    return Object.freeze({machine, params, init: () => runtime.init(params), step: (state: State, request: Request) => runtime.step(params, state, request)})
  }
  const functionInstances: FunctionInstanceSpec = {sorts: signature.sorts, functions: {...signature.symbols, ...Object.fromEntries(signature.axioms.map(ax => [auxiliaries[ax.name]!, {args: ax.forall.map(b => b.sort), result: ax.exists.sort}]))}}
  return Object.freeze({instancePrecondition: freeze(signature), abstractMachine: freeze(m), auxiliaries: freeze(auxiliaries), functionInstances: freeze(functionInstances), bind})
}
