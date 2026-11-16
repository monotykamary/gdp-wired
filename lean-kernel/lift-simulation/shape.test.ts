import {describe,expect,test} from 'bun:test'
import type {C,E,Machine,Law} from '../../core/machine.ts'
import {sumMachine} from '../../kernel/kernel.ts'
import {planRadixSimulation,type RadixSimulationBundle} from './shape.ts'
import type {GenericLiftSource} from '../lift/source.ts'
const v=(name:string):E=>({op:'var',name}),n=(value:number):E=>({op:'const',value})
const get=(map:string,key:E):E=>({op:'get',map,key})
const eq=(a:E,b:E):C=>({op:'=',a,b})
function fixture(radix=19,cell='Edges',unary='Owners'):{bundle:RadixSimulationBundle,source:GenericLiftSource}{
 const pair:E={op:'tup',a:v('from'),b:v('to')},old:E={op:'add',a:{op:'mul',k:radix,a:v('from')},b:v('to')}
 const publicLaw:Law={name:'exclusive',forall:'a',keys:['b'],holds:{op:'or',xs:[{op:'not',x:{op:'and',xs:[eq(get(unary,v('a')),n(1)),eq(get(unary,v('b')),n(1))]}},eq(v('a'),v('b'))]}}
 const base:Machine={name:'retained',params:[],inputs:['from','to'],state:{on:n(0)},maps:{[cell]:0,[unary]:0},step:{maps:{[cell]:{key:old,value:n(1)}}},sums:{total:{key:'sumAddress',term:get(unary,v('sumAddress'))}}}
 const laws:Law[]=[{name:'edge-kind',forall:'edge',holds:{op:'<=',a:get(cell,v('edge')),b:n(1)}},{name:'owner-kind',forall:'owner',holds:{op:'<=',a:get(unary,v('owner')),b:n(1)}},publicLaw]
 const producer=sumMachine(base).machine
 const proof={instances:Object.fromEntries(laws.map(l=>[l.name,{}])),trees:Object.fromEntries(laws.flatMap(l=>['start','step'].map(s=>[l.name+' @'+s,{}])))} as any
 const source:GenericLiftSource={schema:'gdp-lift-source/v1',id:'arbitrary',machine:{...base,sums:undefined,step:{maps:{[cell]:{key:pair,value:n(1)}}}},laws:[publicLaw]}
 const bundle:RadixSimulationBundle={original:{machine:base,laws:[publicLaw]},verdict:{proven:true,checked:true},proof:{kind:'usual',machine:producer,laws,proof}}
 return {bundle,source}
}
describe('radix shape planning is data-driven',()=>{
 test('derives nonhistorical radix and names',()=>{const f=fixture();const p=planRadixSimulation(f.bundle,f.source)!;expect(p.radix).toBe(19);expect(p.layouts).toEqual([{map:'Edges',arity:2}]);expect(p.publicLawIndices).toEqual([2]);expect(p.booleanEntries).toHaveLength(2)})
 test('renaming maps and changing radix does not dispatch by identity',()=>{const f=fixture(31,'Packets','Locks');f.source.id='renamed';expect(planRadixSimulation(f.bundle,f.source)!.layouts[0]).toEqual({map:'Packets',arity:2})})
 test('provided source SUM declarations are never dropped',()=>{const f=fixture();f.source.machine.sums={extra:{key:'at',term:get('Owners',v('at'))}};expect(()=>planRadixSimulation(f.bundle,f.source)).toThrow('source SUM semantics')})
 test('noncandidate returns null',()=>{const f=fixture();f.bundle.proof=undefined;expect(planRadixSimulation(f.bundle,f.source)).toBeNull()})
 test('candidate without checked verdict throws',()=>{const f=fixture();f.bundle.verdict.checked=false;expect(()=>planRadixSimulation(f.bundle,f.source)).toThrow('unverified')})
 test('missing SUM declarations throws, not fallback',()=>{const f=fixture();f.bundle.original.machine={...f.bundle.original.machine,sums:undefined};expect(()=>planRadixSimulation(f.bundle,f.source)).toThrow('SUM declarations')})
 test('missing primary tree throws',()=>{const f=fixture();if(f.bundle.proof?.kind==='usual')delete f.bundle.proof.proof.trees['exclusive @step'];expect(()=>planRadixSimulation(f.bundle,f.source)).toThrow('primary obligation')})
 test('missing checked Boolean bound throws',()=>{const f=fixture();if(f.bundle.proof?.kind==='usual')f.bundle.proof.laws=f.bundle.proof.laws.filter(l=>l.name!=='edge-kind');expect(()=>planRadixSimulation(f.bundle,f.source)).toThrow('Boolean')})
 test('wrong tuple arity throws',()=>{const f=fixture();f.source.machine.step.maps!.Edges={key:{op:'tup',a:v('from'),b:{op:'tup',a:v('to'),b:n(0)}},value:n(1)};expect(()=>planRadixSimulation(f.bundle,f.source)).toThrow('arity mismatch')})
 test('mixed radix throws',()=>{const f=fixture();if(f.bundle.proof?.kind==='usual')f.bundle.proof.machine.step.state={other:get('Edges',{op:'add',a:{op:'mul',k:7,a:v('from')},b:v('to')})};expect(()=>planRadixSimulation(f.bundle,f.source)).toThrow('ambiguous')})
})
