import {expect,test} from 'bun:test'
import {all,any,atMost,get,ite,less,n,not,plus,same,x,type Machine} from '../machine.ts'
import {canon,check,type Path} from '../../kernel/kernel.ts'
import {clock,grow} from '../../kernel/prove.ts'
import {activeWriteKey,activeWriteRow,proveRowCases,rowPairs} from './row-cases.ts'
test('active writes select the destination row rather than the copied source',()=>{
 const m:Machine={name:'copy row',params:[],inputs:['action','source','destination'],state:{},maps:{Clock:0},step:{flags:{moving:same(x('action'),n(2))},maps:{Clock:{each:'k',value:ite(all({op:'flag',name:'moving'},same(x('k'),x('destination'))),get('Clock',x('source')),get('Clock',x('k')))}}}}
 const at=(value:number):Path=>{const a={action:1,'1':-value},b={action:-1,'1':value};return new Map([[canon(a),{lin:a,holds:true}],[canon(b),{lin:b,holds:true}]])}
 expect(activeWriteRow(m,at(2))).toBe('destination')
 expect(activeWriteRow(m,at(3))).toBeUndefined()
})
test('Boolean-valued row writes ignore dead arms and membership lookup keys',()=>{
 const moving={op:'flag' as const,name:'moving'},k=x('k'),a=x('a'),z=x('z'),m:Machine={name:'bit copy',params:[],inputs:['mode','a','z'],state:{},maps:{Bits:0},step:{flags:{moving:same(x('mode'),n(1))},maps:{Bits:{each:'k',value:ite(any(all(moving,same(k,z),same(get('Bits',a),n(1))),all(not(moving),atMost(a,k),less(k,plus(a,n(1))),same(get('Bits',k),n(1)))),n(1),n(0))}}}}
 const x1={mode:1,'1':-1},x2={mode:-1,'1':1},root:Path=new Map([[canon(x1),{lin:x1,holds:true}],[canon(x2),{lin:x2,holds:true}]])
 expect(activeWriteRow(m,root)).toBe('z')
})
test('active constant-index writes split against that index, not an unrelated input',()=>{
 const m:Machine={name:'initial row',params:[],inputs:['actor'],state:{},maps:{Version:0},step:{maps:{Version:{each:'row',value:ite(same(x('row'),n(0)),n(1),get('Version',x('row')))}}}}
 const claim=same(get('Version',x('left')),get('Version',x('right')))
 expect(activeWriteKey(m,new Map())).toEqual(n(0))
 expect(rowPairs(m,{reads:[]},new Map(),claim)).toEqual([[x('left'),n(0)],[x('right'),n(0)]])
})

test('field-only conclusions discover row cases without a post-count read',()=>{
 const destination=x('destination'),m:Machine={name:'field copy',params:['size'],inputs:['source','destination'],state:{},maps:{Clock:0,Untouched:0},step:{maps:{Clock:{each:'k',value:ite(same(x('k'),destination),get('Clock',x('source')),get('Clock',x('k')))}}}}
 const claim=same(get('Clock',x('left')),get('Clock',x('right')))
 expect(rowPairs(m,{reads:[]},new Map(),claim)).toEqual([[x('left'),destination],[x('right'),destination]])
 expect(rowPairs(m,{reads:[]},new Map(),same(get('Untouched',x('other')),n(0)))).toEqual([])
 expect(rowPairs(m,{reads:[]},new Map(),same(get('Clock',x('source')),get('Clock',x('size'))))).toEqual([])
})

test('row cases cover both directions of disequality and reuse only checked trees',()=>{
 const g={name:'false',hyps:[{op:'<=' as const,a:n(1),b:n(0)}]},events:object[]=[];let calls=0
 const tree=proveRowCases(g,new Map(),[[x('a'),x('i')],[x('b'),x('i')]],clock()+1000,(path,until)=>{calls++;const out=grow(g,path,{nodes:0,until});return 'tree'in out?out.tree:undefined},e=>events.push(e))
 expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)
 expect(calls).toBe(3);expect(events.length).toBeGreaterThan(calls)
})
test('row copies can split the secondary key in the primary-equal branch too',()=>{
 const g={name:'four cases',hyps:[{op:'<' as const,a:n(1),b:n(0)}]};let calls=0
 const tree=proveRowCases(g,new Map(),[[x('a'),x('destination')],[x('b'),x('destination')]],clock()+1000,(path,until)=>{calls++;const out=grow(g,path,{nodes:0,until});return 'tree'in out?out.tree:undefined},undefined,{splitEqual:true})
 expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)
 expect(calls).toBe(4)
})
test('row cases never accept an unchecked leaf',()=>{
 const g={name:'possible',hyps:[{op:'<=' as const,a:n(0),b:x('a')}]}
 expect(proveRowCases(g,new Map(),[[x('a'),x('i')]],clock()+100,()=>({leaf:[]}))).toBeUndefined()
})
test('deferred row proposals still require the composing kernel check',()=>{
 const g={name:'possible',hyps:[{op:'<=' as const,a:n(0),b:x('a')}]}
 const events:any[]=[],tree=proveRowCases(g,new Map(),[[x('a'),x('i')],[x('b'),x('i')]],clock()+1000,()=>({leaf:[]}),event=>events.push(event),{deferToCaller:true})
 expect(tree).toBeDefined()
 expect(events.some(e=>e.cached&&e.proposed&&!e.checked&&e.deferred)).toBe(true)
 if(tree)expect(check(g,tree)).toBe(false)
})
