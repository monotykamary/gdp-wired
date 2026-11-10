import {expect,test} from 'bun:test'
import {any,n,not,same,x,type Machine} from '../machine.ts'
import {canon,check,type Path} from '../../kernel/kernel.ts'
import {clock} from '../../kernel/prove.ts'
import {guardCases} from './guard-cases.ts'
const m:Machine={name:'guard scope',params:[],inputs:['action'],state:{},step:{}}
for(const positive of [true,false])test(`default Boolean activation covers both branches (impossible=${positive})`,()=>{
 const g={name:'Boolean scope',hyps:[positive?{op:'<' as const,a:n(1),b:n(0)}:same(x('action'),n(1))]},guard=any(same(x('action'),n(1)),not(same(x('action'),n(2))))
 const tree=guardCases(m,[],g,{reads:[],insts:[]},guard,clock()+1000,[])
 if(positive){expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)}else expect(tree).toBeUndefined()
})
test('activation proofs retain their original non-empty path scope',()=>{
 const lin={action:1},path:Path=new Map([[canon(lin),{lin,holds:true}]]),g={name:'scoped',hyps:[same(x('action'),n(1))]}
 const tree=guardCases(m,[],g,{reads:[],insts:[]},same(x('action'),n(1)),clock()+1000,[],0,path)
 expect(tree).toBeDefined();if(tree)expect(check(g,tree,path)).toBe(true)
})
for(const deferred of [false,true])test(`activation proposals pass the complete source check (deferred=${deferred})`,()=>{
 const g={name:'impossible',hyps:[{op:'<' as const,a:n(1),b:n(0)}]},before=JSON.stringify(g),events:any[]=[]
 const tree=guardCases(m,[],g,{reads:[],insts:[]},same(x('action'),n(1)),clock()+1000,events,0,new Map(),{deferCheck:deferred})
 expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)
 expect(events.some(e=>e.stage==='guard-complete'&&(deferred?e.proposed&&e.deferred&&!e.checked:e.checked))).toBe(true)
 expect(JSON.stringify(g)).toBe(before)
})
