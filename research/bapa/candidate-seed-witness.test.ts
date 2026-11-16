import {expect,test} from 'bun:test'
import type {C,E,Law,Machine} from '../../core/machine.ts'
import {substC} from '../../kernel/kernel.ts'
import {adaptCandidateSeedWitness,type RetainedWitnessContext} from './candidate-seed-witness.ts'
const v=(name:string):E=>({op:'var',name}),n=(value:number):E=>({op:'const',value})
const get=(map:string,key:E):E=>({op:'get',map,key})
const tuple=(a:E,b:E):E=>({op:'tup',a,b})
const add=(a:E,b:E):E=>({op:'add',a,b}),mul=(k:number,a:E):E=>({op:'mul',k,a})
const present=(a:E):C=>({op:'<=',a:n(1),b:a})
const truth:C={op:'<=',a:n(0),b:n(0)}
const bindings={maps:{Owner:{target:'Owner',sorts:['Key','Node'],radix:64},TransferMsg:{target:'TransferMsg',sorts:['Node','Key','Value'],radix:64}},domains:{Key:'keys',Node:'nodes',Value:'values'},fields:{'Owner$n':{relation:'Owner',keyPositions:[0],valuePosition:1}}}
function fixture(){
 const source:Machine={name:'old',params:['keys'],inputs:['k','n','n2','v'],state:{},maps:{Owner:0,TransferMsg:0},step:{}}
 const old:Law={name:'safety',forall:'oldKey',some:['oldOwner','oldMessage'],holds:{op:'or',xs:[{op:'and',xs:[{op:'<',a:v('oldOwner'),b:n(64)},present(get('Owner',add(mul(64,v('oldKey')),v('oldOwner'))))]},present(get('TransferMsg',v('oldMessage')))]}}
 const sub={'oldOwner':get('Owner$n',v('oldKey')),'oldMessage':add(add(mul(4096,get('TransferMsg$n21',v('oldKey'))),mul(64,v('oldKey'))),get('TransferMsg$v1',v('oldKey')))}
 const point=(name:string,value:string,flag:string)=>({start:0,write:{key:v('k'),value:{op:'if' as const,c:{op:'flag' as const,name:flag},then:v(value),else:get(name,v('k'))}}})
 const maps={'Owner$n':point('Owner$n','n','owns'),'TransferMsg$n21':point('TransferMsg$n21','n2','reshards'),'TransferMsg$v1':point('TransferMsg$v1','v','reshards')}
 const plain:Law={name:old.name,forall:old.forall,holds:substC(old.holds,{vars:sub,maps:{},flags:{}})}
 const context:RetainedWitnessContext={original:source,laws:[old],G:{orig:source,vars:{},maps},plains:{[old.name]:{plain,sub}},family:[plain]}
 const target:Machine={name:'native',params:['nodes','keys','values'],inputs:['k','n','n2','v'],state:{},maps:{Owner:0,TransferMsg:0},relations:{Owner:['Key','Node'],TransferMsg:['Node','Key','Value']},step:{flags:{owns:truth,reshards:truth},maps:{Owner:{key:tuple(v('k'),v('n')),value:n(0)},TransferMsg:{key:tuple(v('n2'),tuple(v('k'),v('v'))),value:n(0)}}}}
 const law:Law={name:'safety',forall:'nativeKey',some:['destValue','owner','destNode','destKey'],holds:{op:'or',xs:[{op:'and',xs:[{op:'<',a:v('owner'),b:v('nodes')},present(get('Owner',tuple(v('nativeKey'),v('owner'))))]},{op:'and',xs:[{op:'<',a:v('destNode'),b:v('nodes')},{op:'<',a:v('destKey'),b:v('keys')},{op:'<',a:v('destValue'),b:v('values')},present(get('TransferMsg',tuple(v('destNode'),tuple(v('destKey'),v('destValue')))))]}]}}
 return{context,target,law}
}
test('retained witness coordinates map by roles, not existential binder order',()=>{
 const {context,target,law}=fixture(),before=JSON.stringify([context,target,law])
 const out=adaptCandidateSeedWitness(context,target,[law],bindings),terms=out.witnesses.safety!.terms!
 expect(terms.destKey).toEqual(v('nativeKey'))
 expect(terms.owner).toEqual(get(out.audit[0]!.ghostMaps['Owner$n']!,v('nativeKey')))
 expect(terms.destNode).toEqual(get(out.audit[0]!.ghostMaps['TransferMsg$n21']!,v('nativeKey')))
 expect(terms.destValue).toEqual(get(out.audit[0]!.ghostMaps['TransferMsg$v1']!,v('nativeKey')))
 expect(Object.keys(out.ghosts.maps)).toHaveLength(3)
 expect(out.audit[0]).toMatchObject({sourceVariables:2,targetVariables:4,helperMode:'guarded-equality',trusted:false})
 expect(out.bindings.fields?.['Owner$n']).toBeUndefined()
 expect(out.laws[0]!.holds.op).toBe('or')
 expect(JSON.stringify([context,target,law])).toBe(before)
})
test('malformed coordinate coefficients, target layouts, and ghost flags fail closed',()=>{
 const a=fixture(),wrong=structuredClone(a.context)
 const e=wrong.plains.safety!.sub.oldMessage!
 if(e.op!=='add'||e.a.op!=='add'||e.a.a.op!=='mul')throw Error('bad fixture')
 e.a.a.k=4097
 expect(()=>adaptCandidateSeedWitness(wrong,a.target,[a.law],bindings)).toThrow('coefficient')
 expect(()=>adaptCandidateSeedWitness(a.context,{...a.target,relations:{...a.target.relations,Owner:['Node','Key']}},[a.law],bindings)).toThrow('layout')
 const badFlag=structuredClone(a.context)
 ;(badFlag.G.maps['Owner$n']!.write as {value:Extract<E,{op:'if'}>}).value.c={op:'flag',name:'missing'}
 expect(()=>adaptCandidateSeedWitness(badFlag,a.target,[a.law],bindings)).toThrow('flag')
})
