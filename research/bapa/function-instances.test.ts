import {test, expect} from 'bun:test'
import {argsKey, type E, type C, type Law, type Machine} from '../../core/machine.ts'
import {checkLaws} from '../../kernel/kernel.ts'
import {proveLaws} from '../../kernel/prove.ts'
import {extendFunctionInstances, functionInstanceProgress, hasFunctionInstances, withFunctionInstances, type FunctionInstanceSpec} from '../../kernel/function-instances.ts'
import {rigidMinimal, rigidMinimalLaw} from './rigid-minimal.ts'
const v = (name: string): E => ({op: 'var', name}), k = (value: number): E => ({op: 'const', value})
const call = (map: string, ...args: E[]): E => ({op: 'get', map, key: argsKey(args)})
const eq = (a: E, b: E): C => ({op: '=', a, b})
const guard = (keys: string[]): C => ({op: 'and', xs: keys.map(name => ({op: '<', a: v(name), b: v('size')}))})
const fixture = (keys: string[], body: C, arity = keys.length) => {
  const fact: Law = {name: 'source', forall: keys[0], keys: keys.slice(1), holds: {op: 'or', xs: [{op: 'not', x: guard(keys)}, body]}}
  const machine: Machine = {name: 'trigger-control', params: ['size'], inputs: [], state: {}, step: {}, fns: {F: {js: '() => 0', arity}}, facts: [fact]}
  const spec: FunctionInstanceSpec = {sorts: {S: 'size'}, functions: {F: {args: Array.from({length: arity}, () => 'S')}}, limits: {tuples: 1000}}
  return {machine, spec}
}
const discover = (m: Machine, spec: FunctionInstanceSpec, hyps: C[]) => withFunctionInstances(spec, () => extendFunctionInstances(m, {}, [{name: 'scope', hyps}]))

test('default OFF keeps the old result; opt-in closes unseeded minimal without new facts', () => {
  const p = rigidMinimal(), before = JSON.stringify(p.abstractMachine)
  const off = proveLaws(p.abstractMachine, [rigidMinimalLaw])
  expect(off.proven).toBe(false)
  const on = withFunctionInstances(p.functionInstances, () => proveLaws(p.abstractMachine, [rigidMinimalLaw]))
  expect(on.status).toBe('complete')
  if (on.status !== 'complete') throw Error(on.reason)
  expect(on.value).toMatchObject({proven: true, checked: true})
  expect(on.value.proof && checkLaws(p.abstractMachine, [rigidMinimalLaw], on.value.proof)).toBe(true)
  expect(JSON.stringify(p.abstractMachine)).toBe(before)
  expect(proveLaws(p.abstractMachine, [rigidMinimalLaw])).toEqual(off)
})
test('read-only progress snapshot cannot mutate active search and is absent outside its scope', () => {
  const p=rigidMinimal()
  expect(functionInstanceProgress()).toBeUndefined()
  const r=withFunctionInstances(p.functionInstances,()=>{
    const x=functionInstanceProgress()!
    ;(x as {work:number}).work=1_000_000
    expect(functionInstanceProgress()!.work).toBe(0)
    return true
  })
  expect(r.status).toBe('complete')
  expect(functionInstanceProgress()).toBeUndefined()
})
test('sort-derived bootstrap does not depend on a literal zero in the law', () => {
  const p = rigidMinimal(), law: Law = {name: 'positive without zero', holds: {op: 'or', xs: [{op: 'not', x: {op: '<=', a: k(1), b: v('quorums')}}, {op: '<=', a: k(1), b: v('nodes')}]}}
  const on = withFunctionInstances(p.functionInstances, () => proveLaws(p.abstractMachine, [law]))
  expect(on.status === 'complete' && on.value.proven && on.value.checked).toBe(true)
})
test('off-diagonal three-argument tuples retain head, arity and order', () => {
  const {machine, spec} = fixture(['a','b','c'], eq(call('F',v('a'),v('b'),v('c')),k(0)))
  const r = discover(machine,spec,[eq(call('F',v('x'),v('y'),v('z')),k(0)), eq(call('Wrong',v('u'),v('v'),v('w')),k(0))])
  expect(r.status).toBe('complete')
  if(r.status !== 'complete') throw Error(r.reason)
  expect(r.value.source!.slice(0,3)).toEqual([v('x'),v('y'),v('z')])
  expect(r.stats.matched).toBeGreaterThan(0)
  expect(JSON.stringify(r.value)).not.toContain('"name":"u"')
})
test('repeated pattern variables must agree', () => {
  const {machine,spec} = fixture(['a'], eq(call('F',v('a'),v('a')),k(0)),2)
  const r=discover(machine,spec,[eq(call('F',v('x'),v('y')),k(0))])
  expect(r.status === 'complete' && r.stats.matched).toBe(0)
})
test('a covering pattern set joins compatible partial bindings', () => {
  const {machine,spec}=fixture(['a','b'],{op:'and',xs:[eq(call('F',v('a')),k(0)),eq(call('F',v('b')),k(1))]},1)
  const r=discover(machine,spec,[eq(call('F',v('x')),k(0)),eq(call('F',v('y')),k(1))])
  expect(r.status==='complete' && r.stats.matched>0).toBe(true)
})
test('proof-side map values are quorum candidates; bound variables do not escape', () => {
  const p=rigidMinimal(), spec={...p.functionInstances,maps:{learnedQuorum:{result:'Quorum'}}}
  const g=call('learnedQuorum',v('value'))
  const r=discover(p.abstractMachine,spec,[eq(g,g),{op:'all',key:'hidden',c:eq(call('learnedQuorum',v('hidden')),k(0))}])
  expect(r.status).toBe('complete')
  if(r.status!=='complete') throw Error(r.reason)
  const ax=p.abstractMachine.facts!.find(f=>f.name.includes('axiom'))!
  expect(r.value[ax.name]!.slice(0,2)).toEqual([g,g])
  expect(JSON.stringify(r.value)).not.toContain('hidden')
})
test('typed ghost-map keys do not amplify encoded pairs from legacy helper instances', () => {
  const p=rigidMinimal(), good=call('learnedQuorum',v('value')), bad=call('learnedQuorum',argsKey([v('node'),v('quorum')]))
  const spec={...p.functionInstances,maps:{learnedQuorum:{result:'Quorum',args:['Value']}},variables:{value:'Value',node:'Node',quorum:'Quorum'}}
  const r=discover(p.abstractMachine,spec,[eq(good,bad),eq(call('member',v('node'),bad),k(1))])
  expect(r.status).toBe('complete')
  if(r.status!=='complete') throw Error(r.reason)
  expect(JSON.stringify(r.value)).not.toContain(JSON.stringify(bad))
  expect(JSON.stringify(r.value)).toContain(JSON.stringify(good))
})
test('constant-folded tuples and nested triggers preserve the same function head and arity', () => {
  const {machine,spec}=fixture(['a','b'],eq(call('F',call('G',v('a')),v('b')),k(0)),2)
  machine.fns!.G={js:'x => x'}
  const r=discover(machine,{...spec,functions:{...spec.functions,G:{args:['S']}}},[eq(call('F',call('G',k(3)),k(5)),k(0))])
  expect(r.status==='complete' && r.stats.matched>0).toBe(true)
  if(r.status==='complete') expect(r.value.source!.slice(0,2)).toEqual([k(3),k(5)])
})
test('deep structurally equal terms use bounded exact identities, not recursive escaping', () => {
  const {machine,spec}=fixture(['a'],eq(call('F',v('a'),v('a')),k(0)),2)
  let deep:E=v('x')
  for(let i=0;i<24;i++) deep={op:'add',a:deep,b:k(1)}
  const r=discover(machine,{...spec,limits:{work:100_000}},[eq(call('F',deep,structuredClone(deep)),k(0))])
  expect(r.status).toBe('complete')
  expect(r.status==='complete' && r.stats.matched>0).toBe(true)
  expect(r.stats.work).toBeLessThan(100_000)
})
test('duplicate goal hypotheses do not multiply matching or closure', () => {
  const {machine,spec}=fixture(['a','b'],eq(call('F',v('a'),v('b')),k(0)),2)
  const c=eq(call('F',v('x'),v('y')),k(0)), once=discover(machine,spec,[c]), many=discover(machine,spec,Array.from({length:500},()=>c))
  expect(once.status).toBe('complete')
  expect(many.status).toBe('complete')
  if(once.status==='complete' && many.status==='complete') expect(many.value).toEqual(once.value)
  expect(many.stats.matched).toBe(once.stats.matched)
  expect(many.stats.work-once.stats.work).toBeLessThan(2000)
})
test('cyclic signatures stop at an explicit depth limit and report not proven', () => {
  const {machine,spec}=fixture(['a'],eq(call('F',v('a')),k(0)),1)
  const r=discover(machine,{...spec,functions:{F:{args:['S'],result:'S'}},limits:{depth:2,candidates:30}},[])
  expect(r).toMatchObject({status:'limited',proven:false,checked:false,reason:'function-instantiation cyclic depth limit'})
})
test('charged work/candidate/tuple caps fail closed and context is restored', () => {
  const p=rigidMinimal()
  const r=withFunctionInstances({...p.functionInstances,limits:{work:1}},()=>proveLaws(p.abstractMachine,[rigidMinimalLaw]))
  expect(r).toMatchObject({status:'limited',proven:false,checked:false})
  expect(hasFunctionInstances(p.abstractMachine)).toBe(false)
})
test('each omitted membership conjunct cannot be recovered from the other', () => {
  for(const missing of [1,2]) {
    const p=rigidMinimal(), m=structuredClone(p.abstractMachine), ax=m.facts!.find(f=>f.name.includes('axiom'))!
    const conjunction=(ax.holds as Extract<C,{op:'or'}>).xs[1] as Extract<C,{op:'and'}>
    conjunction.xs.splice(missing,1)
    const choice=call(p.auxiliaries.intersection!,k(0),k(1))
    const law:Law={name:'missing member',holds:{op:'or',xs:[{op:'not',x:{op:'<',a:k(1),b:v('quorums')}},eq(call('member',choice,k(missing===1?0:1)),k(1))]}}
    const r=withFunctionInstances(p.functionInstances,()=>proveLaws(m,[law]))
    expect(r.status==='limited' || !r.value.proven).toBe(true)
  }
})
test('no matching function head yields no matched tuple; non-rigid machines stay off', () => {
  const {machine,spec}=fixture(['a'],eq(call('F',v('a')),k(0)),1)
  const r=discover(machine,spec,[eq(call('Other',v('x')),k(0))])
  expect(r.status==='complete' && r.stats.matched).toBe(0)
  const plain={...machine,facts:[]}
  const state=withFunctionInstances(spec,()=>hasFunctionInstances(plain))
  expect(state.status==='complete' && state.value).toBe(false)
})
test('omitted source axiom or witness range is not repaired by discovery', () => {
  const p=rigidMinimal(), ax=p.abstractMachine.facts!.find(f=>f.name.includes('axiom'))!
  const noAx={...p.abstractMachine,facts:p.abstractMachine.facts!.filter(f=>f!==ax)}
  const noRange=structuredClone(p.abstractMachine), f=noRange.facts!.find(f=>f.name===ax.name)!
  const disj=f.holds as Extract<C,{op:'or'}>, body=disj.xs[1] as Extract<C,{op:'and'}>
  body.xs.shift()
  for(const m of [noAx,noRange]) {
    const r=withFunctionInstances(p.functionInstances,()=>proveLaws(m,[rigidMinimalLaw]))
    expect(r.status==='limited' || !r.value.proven).toBe(true)
  }
})
