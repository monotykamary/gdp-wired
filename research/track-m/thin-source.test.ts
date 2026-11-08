import {expect,test} from 'bun:test'
import {all,atMost,n,x,type Machine} from '../../core/machine.ts'
import {thinFlagInstances,thinLawInstances} from './thin-source.ts'
import {rebasePath} from './rebase-path.ts'
import {assumed,check,type Tree} from '../../kernel/kernel.ts'
import {clock,rowsAt} from '../../kernel/prove.ts'
test('unused flag tuples are removed as whole tuples, unknown layouts are retained',()=>{
 const m:Machine={name:'flags',params:[],inputs:[],state:{},step:{flags:{q:{op:'all',key:'a',keys:['b'],c:all()},r:{op:'all',key:'k',c:all()}}}},at={'?q':[x('a1'),x('b1'),x('a2'),x('b2')],'?r':[x('r1')]},g={name:'flag layout',hyps:[atMost(x('?q'),n(1)),all(),all()]}
 const thin=thinFlagInstances(m,g,at,new Set([2]))
 expect(thin['?q']).toEqual([x('a2'),x('b2')]);expect(thin['?r']).toEqual(at['?r']);expect(at['?q']).toHaveLength(4)
})
test('a smaller source context must preserve every input row of the proof',()=>{
 const original={name:'large',hyps:[atMost(n(0),x('unused')),atMost(n(1),n(0))]},small={name:'small',hyps:[atMost(n(1),n(0))]},root=new Map(),rows=rowsAt(original,root),tree:Tree={leaf:[{kind:'input',index:rows.findIndex(r=>r.lin['1']===1&&Object.keys(r.lin).length===1)}]}
 const rebased=rebasePath(original,tree,root,root,clock()+1000,small)
 expect(rebased).toBeDefined();if(rebased)expect(check(small,rebased)).toBe(true)
 expect(rebasePath(original,tree,root,root,clock()+1000,{name:'possible',hyps:[]})).toBeUndefined()
})
test('unused invariant tuples are removed only when their exact source hypothesis is known',()=>{
 const law={name:'rows',forall:'a',keys:['b'],holds:atMost(x('a'),x('b'))},at={rows:[x('a1'),x('b1'),x('a2'),x('b2')]},goal={name:'rows',hyps:assumed([law],at)}
 expect(thinLawInstances([law],goal,at,new Set([1])).rows).toEqual([x('a2'),x('b2')])
 expect(thinLawInstances([law],{name:'unknown shape',hyps:[]},at,new Set()).rows).toEqual(at.rows)
 expect(at.rows).toHaveLength(4)
})
