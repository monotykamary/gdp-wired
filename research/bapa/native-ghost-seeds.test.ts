import {expect,test} from 'bun:test'
import type {C,E,Law,Machine} from '../../core/machine.ts'
import {substC} from '../../kernel/kernel.ts'
import {adaptNativeGhostSeeds} from './native-ghost-seeds.ts'
import type {RetainedWitnessContext} from './candidate-seed-witness.ts'
const v=(name:string):E=>({op:'var',name}),n=(value:number):E=>({op:'const',value})
const t=(a:E,b:E):E=>({op:'tup',a,b}),get=(map:string,key:E):E=>({op:'get',map,key}),has=(map:string,key:E):C=>({op:'<=',a:n(1),b:get(map,key)})
const bindings={maps:{R:{target:'Receipts',sorts:['Node','Response'],radix:64},Sent:{target:'Requests',sorts:['Node','Request'],radix:64},Match:{target:'Matches',sorts:['Request','Response'],radix:64}},domains:{Node:'nodes',Request:'requests',Response:'responses'}}
const specs={W:{sorts:['Node','Response'],valueSort:'Request'}}
function fixture(){
 const old:Law={name:'matched',forall:'a',keys:['b'],some:['x'],holds:{op:'or',xs:[{op:'not',x:has('R',t(v('a'),v('b')))},{op:'and',xs:[has('Sent',t(v('a'),v('x'))),has('Match',t(v('x'),v('b')))]}]}}
 const sub={x:get('W',t(v('a'),v('b')))},plain:Law={name:old.name,forall:old.forall,keys:old.keys,holds:substC(old.holds,{vars:sub,maps:{},flags:{}})}
 const source:Machine={name:'old',params:[],inputs:['n','r','p'],state:{},maps:{R:0,Sent:0,Match:0},step:{}}
 const G={orig:source,vars:{},maps:{W:{start:0,write:{key:t(v('n'),v('p')),value:{op:'if' as const,c:{op:'flag' as const,name:'respond'},then:v('r'),else:get('W',t(v('n'),v('p')))}}}}}
 const context:RetainedWitnessContext={original:source,laws:[old],G,plains:{matched:{plain,sub}},family:[plain]}
 const target:Machine={name:'native',params:['nodes','requests','responses'],inputs:['n','r','p'],state:{},maps:{Receipts:0,Requests:0,Matches:0},relations:{Receipts:['Node','Response'],Requests:['Node','Request'],Matches:['Request','Response']},step:{flags:{respond:{op:'=',a:n(0),b:n(0)}},maps:{Receipts:{key:t(v('n'),v('p')),value:n(1)},Requests:{key:t(v('n'),v('r')),value:n(1)},Matches:{key:t(v('r'),v('p')),value:n(1)}}}}
 const law:Law={name:'matched',forall:'response',keys:['node'],some:['request'],holds:{op:'or',xs:[{op:'not',x:has('Receipts',t(v('node'),v('response')))},{op:'and',xs:[has('Requests',t(v('node'),v('request'))),has('Matches',t(v('request'),v('response')))]}]}}
 return{context,target,law}
}
test('native binary ghost keys and public witness bind by relation role, not binder order',()=>{
 const f=fixture(),before=JSON.stringify(f),out=adaptNativeGhostSeeds(f.context,f.target,[f.law],bindings,specs),alias=out.audit[0]!.ghostMaps.W!
 expect(out.witnesses.matched!.terms!.request).toEqual(get(alias,t(v('node'),v('response'))))
 expect(out.ghosts.maps[alias]!.write).toMatchObject({key:t(v('n'),v('p'))})
 expect(out.bindings.maps.W!.sorts).toEqual(['Node','Response'])
 expect(Object.values(out.bindings.variables??{})).toContainEqual({sort:'Request',radix:64})
 expect(out.laws[0]!.keys).toHaveLength(2)
 expect(out.audit[0]).toMatchObject({trusted:false,sourceVariables:1,targetVariables:1})
 expect(JSON.stringify(f)).toBe(before)
})
test('native ghost transport refuses wrong roles, nonzero starts, missing ghosts and flags',()=>{
 const f=fixture(),wrong=structuredClone(f.context);wrong.G.maps.W!.start=1
 expect(()=>adaptNativeGhostSeeds(wrong,f.target,[f.law],bindings,specs)).toThrow('zero-start')
 expect(()=>adaptNativeGhostSeeds(f.context,f.target,[f.law],bindings,{})).toThrow('complete producer')
 expect(()=>adaptNativeGhostSeeds(f.context,{...f.target,relations:{...f.target.relations,Receipts:['Response','Node']}},[f.law],bindings,specs)).toThrow('layout')
 const bad=structuredClone(f.context);const write=bad.G.maps.W!.write;if(!('key'in write)||write.value.op!=='if')throw Error('bad fixture');write.value.c={op:'flag',name:'unknown'}
 expect(()=>adaptNativeGhostSeeds(bad,f.target,[f.law],bindings,specs)).toThrow('flag')
})
