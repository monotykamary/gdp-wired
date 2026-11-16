import {expect,test} from 'bun:test'
import type {Law} from '../../core/machine.ts'
import {abstractWitnessValues} from './witness-value-proxies.ts'

const bindings={maps:{'Owner$n':{target:'fresh',sorts:['Key'],radix:64}},domains:{Key:'keys',Node:'nodes'},fields:{'Owner$n':{relation:'Owner',keyPositions:[0],valuePosition:1}}}
const cell={op:'get' as const,map:'Owner$n',key:{op:'var' as const,name:'k'}}
const law:Law={name:'repeat',forall:'k',keys:['seed$ghost$value$0'],holds:{op:'=',a:cell,b:cell}}

test('ghost cells use one shared universally guarded value, not a relation row',()=>{
 const result=abstractWitnessValues([law],bindings,{'Owner$n':'Node'})
 const out=result.laws[0]!, name=out.keys![1]!
 expect(name).toBe('seed$ghost$value$1')
 expect(out.keys![0]).toBe('seed$ghost$value$0')
 expect(out.holds).toEqual({op:'or',xs:[{op:'not',x:{op:'=',a:cell,b:{op:'var',name}}},{op:'=',a:{op:'var',name},b:{op:'var',name}}]})
 expect(result.bindings.variables![name]).toEqual({sort:'Node',radix:64})
 expect(result.bindings.fields!['Owner$n']).toBeUndefined()
 expect(bindings.fields['Owner$n']).toBeDefined()
})

test('rejects non-bound ghost keys, wrong key arities and unknown value sorts',()=>{
 expect(()=>abstractWitnessValues([{...law,forall:'other'}],bindings,{'Owner$n':'Node'})).toThrow('unbound ghost key')
 expect(()=>abstractWitnessValues([law],bindings,{'Owner$n':'Missing'})).toThrow('invalid ghost coordinate')
 expect(()=>abstractWitnessValues([law],{...bindings,maps:{'Owner$n':{target:'fresh',sorts:['Key','Node'],radix:64}}},{'Owner$n':'Node'})).toThrow('invalid ghost coordinate')
})
