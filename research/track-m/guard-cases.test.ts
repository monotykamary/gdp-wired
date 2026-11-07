import {expect,test} from 'bun:test'
import {n,same,x,type Machine} from '../../core/machine.ts'
import {canon,check,type Path} from '../../kernel/kernel.ts'
import {clock} from '../../kernel/prove.ts'
import {guardCases} from './guard-cases.ts'
const m:Machine={name:'guard scope',params:[],inputs:['action'],state:{},step:{}}
test('activation proofs retain their original non-empty path scope',()=>{
 const lin={action:1},path:Path=new Map([[canon(lin),{lin,holds:true}]]),g={name:'scoped',hyps:[same(x('action'),n(1))]}
 const tree=guardCases(m,[],g,{reads:[],insts:[]},same(x('action'),n(1)),clock()+1000,[],0,path)
 expect(tree).toBeDefined()
 if(tree)expect(check(g,tree,path)).toBe(true)
})
test('activation cases cannot turn a satisfiable unrestricted goal into a proof',()=>{
 const g={name:'possible',hyps:[same(x('action'),n(1))]}
 expect(guardCases(m,[],g,{reads:[],insts:[]},same(x('action'),n(1)),clock()+1000,[])).toBeUndefined()
})
test('activation case leaves lift to a checked complete tree',()=>{
 const g={name:'impossible',hyps:[{op:'<' as const,a:n(1),b:n(0)}]}
 const tree=guardCases(m,[],g,{reads:[],insts:[]},same(x('action'),n(1)),clock()+1000,[])
 expect(tree).toBeDefined()
 if(tree)expect(check(g,tree)).toBe(true)
})
