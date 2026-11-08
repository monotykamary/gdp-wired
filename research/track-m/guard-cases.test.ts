import {expect,test} from 'bun:test'
import {any,n,not,same,x,type Machine} from '../../core/machine.ts'
import {canon,check,type Path} from '../../kernel/kernel.ts'
import {clock} from '../../kernel/prove.ts'
import {guardCases} from './guard-cases.ts'
const m:Machine={name:'guard scope',params:[],inputs:['action'],state:{},step:{}}
for(const positive of [true,false])test(`Boolean activation ${positive?'covers a disjunction and its complement':'does not prove a possible source'}`,()=>{
 const previous=process.env.LAB_BOOLEAN_GUARDS
 try{
  process.env.LAB_BOOLEAN_GUARDS='1'
  const g={name:'Boolean scope',hyps:[positive?{op:'<' as const,a:n(1),b:n(0)}:same(x('action'),n(1))]},guard=any(same(x('action'),n(1)),not(same(x('action'),n(2))))
  const tree=guardCases(m,[],g,{reads:[],insts:[]},guard,clock()+1000,[])
  if(positive){expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)}else expect(tree).toBeUndefined()
 }finally{if(previous===undefined)delete process.env.LAB_BOOLEAN_GUARDS;else process.env.LAB_BOOLEAN_GUARDS=previous}
})
test('activation proofs retain their original non-empty path scope',()=>{
 const lin={action:1},path:Path=new Map([[canon(lin),{lin,holds:true}]]),g={name:'scoped',hyps:[same(x('action'),n(1))]}
 const tree=guardCases(m,[],g,{reads:[],insts:[]},same(x('action'),n(1)),clock()+1000,[],0,path)
 expect(tree).toBeDefined()
 if(tree)expect(check(g,tree,path)).toBe(true)
})
test('source-only activation stays checked and does not mutate its input goal',()=>{
 const previous=process.env.LAB_ACTIVE_SOURCE
 try{
  process.env.LAB_ACTIVE_SOURCE='1'
  const g={name:'impossible source',hyps:[{op:'<' as const,a:n(1),b:n(0)}]},before=JSON.stringify(g),events:any[]=[]
  const tree=guardCases(m,[],g,{reads:[],insts:[]},same(x('action'),n(1)),clock()+1000,events)
  expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)
  expect(events.some(e=>e.stage==='guard-leaf'&&e.active&&e.sourceOnly)).toBe(true)
  expect(JSON.stringify(g)).toBe(before)
 }finally{if(previous===undefined)delete process.env.LAB_ACTIVE_SOURCE;else process.env.LAB_ACTIVE_SOURCE=previous}
})
test('activation cases cannot turn a satisfiable unrestricted goal into a proof',()=>{
 const g={name:'possible',hyps:[same(x('action'),n(1))]}
 expect(guardCases(m,[],g,{reads:[],insts:[]},same(x('action'),n(1)),clock()+1000,[])).toBeUndefined()
})
test('activation case leaves lift to a checked complete tree',()=>{
 const g={name:'impossible',hyps:[{op:'<' as const,a:n(1),b:n(0)}]}
 const events:any[]=[],tree=guardCases(m,[],g,{reads:[],insts:[]},same(x('action'),n(1)),clock()+1000,events)
 expect(tree).toBeDefined()
 expect(events.some(e=>e.stage==='guard-leaf'&&e.active&&e.deferred&&!e.checked)).toBe(true)
 expect(events.some(e=>e.stage==='guard-complete'&&e.checked)).toBe(true)
 if(tree)expect(check(g,tree)).toBe(true)
})
