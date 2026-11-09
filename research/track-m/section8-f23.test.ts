import {test,expect} from 'bun:test'
import {atMost,n,x} from '../../core/machine.ts'
import {type Goal,type Tree,canon,check} from '../../kernel/kernel.ts'
import {memoIndependent,memoRetarget,slicedCheck} from './section8-f23.ts'
test('F2 slices and reindexes a checked leaf without weakening the final check',()=>{
 const a=x('a'),goal:Goal={name:'slice',hyps:[atMost(x('unused'),n(9)),atMost(a,n(0)),atMost(n(1),a)]}
 const tree:Tree={leaf:[{kind:'input',index:1},{kind:'input',index:2},{kind:'combine',a:0,b:1,ma:1,mb:1}]}
 expect(check(goal,tree)).toBe(true);expect(slicedCheck(goal,tree,new Map())).toBe(true)
 const bad:Tree={leaf:[]};expect(slicedCheck(goal,bad,new Map())).toBe(false);expect(check(goal,bad)).toBe(false)
})
test('F2 preserves ordered path rows',()=>{
 const goal:Goal={name:'path',hyps:[atMost(x('a'),n(0))]},lin={a:1},path=new Map([[canon(lin),{lin,holds:false}]])
 const tree:Tree={leaf:[{kind:'input',index:0},{kind:'input',index:1},{kind:'combine',a:0,b:1,ma:1,mb:1}]}
 expect(check(goal,tree,path)).toBe(true);expect(slicedCheck(goal,tree,path)).toBe(true)
})
test('F3 memo keys include both goals, cut identity and scope',()=>{
 const goal:Goal={name:'x',hyps:[]},other:Goal={name:'y',hyps:[]},cut={when:[],cut:{'1':1},tree:{leaf:[]} as Tree};let n=0
 const compute=()=>{n++;return true};expect(memoIndependent(goal,cut,compute)).toBe(true);expect(memoIndependent(goal,cut,compute)).toBe(true);expect(n).toBe(1)
 const move=()=>{n++;return cut},path=new Map();memoRetarget(goal,other,cut,path,false,move);memoRetarget(goal,other,cut,path,false,move);expect(n).toBe(2)
 memoRetarget(other,goal,cut,path,false,move);expect(n).toBe(3)
})
