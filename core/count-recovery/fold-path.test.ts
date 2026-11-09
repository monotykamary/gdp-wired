import {expect,test} from 'bun:test'
import {all,ite,n,same,x} from '../machine.ts'
import {canon,check,type Path} from '../../kernel/kernel.ts'
import {clock,grow,widen} from '../../kernel/prove.ts'
import {foldPath} from './fold-path.ts'
test('path folding retains a checked route through original conditional terms',()=>{
 const a={op:1,'1':-4},b={op:-1,'1':4},path:Path=new Map([[canon(a),{lin:a,holds:true}],[canon(b),{lin:b,holds:true}]])
 const value=ite(all(same(x('op'),n(4)),same(x('bit'),n(1))),n(2),n(0)),g={name:'original condition',hyps:[{op:'<=' as const,a:value,b:n(1)},same(x('bit'),n(1))]},folded=foldPath(g,path)
 expect(Object.keys(folded.opaque).length).toBeGreaterThan(0)
 const out=grow(folded.goal,path,{nodes:0,until:clock()+1000})
 expect('tree'in out).toBe(true)
 if('tree'in out){const tree=widen(folded.goal,g,out.tree,folded.opaque,path,path);expect(tree).toBeDefined();if(tree)expect(check(g,tree,path)).toBe(true)}
 expect(g.hyps[0]).toEqual({op:'<=',a:value,b:n(1)})
})
