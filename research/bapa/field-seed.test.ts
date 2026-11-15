import {expect,test} from 'bun:test'
import type {E,Law,Machine} from '../../core/machine.ts'
import {restateSeeds,type SeedBindings} from './candidate-seed-restatement.ts'
const v=(name:string):E=>({op:'var',name}),n=(value:number):E=>({op:'const',value})
const get=(map:string):E=>({op:'get',map,key:v('k')})
const source:Machine={name:'old ghosts',params:[],inputs:[],state:{},maps:{'Owner$n':0,'TransferMsg$n21':0,'TransferMsg$v1':0},step:{}}
const target:Machine={name:'native rows',params:['nodes','keys','values'],inputs:[],state:{},maps:{Owner:0,TransferMsg:0},relations:{Owner:['Key','Node'],TransferMsg:['Node','Key','Value']},step:{}}
const bindings:SeedBindings={domains:{Node:'nodes',Key:'keys',Value:'values'},maps:{Owner:{target:'Owner',sorts:['Key','Node'],radix:64},TransferMsg:{target:'TransferMsg',sorts:['Node','Key','Value'],radix:64}},fields:{'Owner$n':{relation:'Owner',keyPositions:[0],valuePosition:1},'TransferMsg$n21':{relation:'TransferMsg',keyPositions:[1],valuePosition:0},'TransferMsg$v1':{relation:'TransferMsg',keyPositions:[1],valuePosition:2}}}
const law:Law={name:'field bounds',forall:'k',holds:{op:'and',xs:['Owner$n','TransferMsg$n21','TransferMsg$v1'].map(map=>({op:'<',a:get(map),b:n(64)}))}}
test('row proposals share tuple coordinates, keep membership guards, and disclose absent-row gap',()=>{
 const [a]=restateSeeds([law],target,bindings,{sourceMachine:source})
 expect(a?.status).toBe('candidate');if(a?.status!=='candidate')throw Error('fields not proposed')
 expect(a.fieldRows).toEqual({kind:'row-guarded-proposal',absence:'not-covered',fields:['Owner$n','TransferMsg$n21','TransferMsg$v1'],rows:2})
 expect([a.law.forall,...a.law.keys!]).toHaveLength(4)
 const text=JSON.stringify(a.law.holds)
 expect(text).not.toContain('Owner$n');expect(text).not.toContain('TransferMsg$n21');expect(text).not.toContain('TransferMsg$v1')
 expect(text).toContain('"name":"nodes"');expect(text).toContain('"name":"values"');expect(text).toContain('"op":"tup"')
 expect(a.law.holds.op).toBe('or');if(a.law.holds.op!=='or')throw Error('row guards missing')
 expect(a.law.holds.xs.slice(0,2).every(c=>c.op==='not')).toBe(true)
})
test('field proposals fail closed on missing declaration or conflicting coordinate layout',()=>{
 expect(restateSeeds([law],target,bindings)[0]?.status).toBe('dropped')
 expect(restateSeeds([law],target,{...bindings,fields:{...bindings.fields,'Owner$n':{relation:'Owner',keyPositions:[0],valuePosition:0}}},{sourceMachine:source})[0]?.status).toBe('dropped')
 expect(restateSeeds([law],{...target,relations:{...target.relations,Owner:['Node','Key']}},bindings,{sourceMachine:source})[0]?.status).toBe('dropped')
})
