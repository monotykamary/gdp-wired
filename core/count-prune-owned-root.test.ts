import {expect,test} from 'bun:test'
import {deferOwnedReplacementChecks} from './count-strategy.ts'
import {atMost,ite,n,x} from './machine.ts'
import {canon,check,type Path,type Tree} from '../kernel/kernel.ts'
import {clock,rowsAt} from '../kernel/prove.ts'
import {rebasePath} from './count-rebase-path.ts'
import {pruneOwnedRoot} from './count-prune-owned-root.ts'
for(const conditional of [false,true])test('structural root pruning preserves required conditions: '+conditional,()=>{
 const atom={lin:{x:1},holds:true},root:Path=new Map([[canon(atom.lin),atom]]),g={name:'root pruning',hyps:conditional?[atMost(x('x'),n(0)),atMost(ite(atMost(x('x'),n(0)),n(1),n(0)),n(0))]:[atMost(n(1),n(0))]}
 const rows=rowsAt(g,root),index=rows.findIndex(r=>r.lin['1']===1&&Object.keys(r.lin).length===1),tree:Tree={leaf:[{kind:'input',index}]}
 expect(check(g,tree,root)).toBe(true)
 const result=pruneOwnedRoot<typeof atom,{tree:Tree,root:Path}>([atom],{tree,root},(kept,previous)=>{const nextRoot:Path=new Map(kept.map(a=>[canon(a.lin),a])),next=rebasePath(g,previous.tree,previous.root,nextRoot,clock()+1000);return next?{tree:next,root:nextRoot}:undefined})
 expect(result.kept).toHaveLength(conditional?1:0);expect(check(g,result.proof.tree,result.proof.root)).toBe(true)
 if(conditional)expect(check(g,tree,new Map())).toBe(false) // unsafely dropped assumption is rejected
})
test('a proposer cannot substitute final native acceptance',()=>{
 const goal={name:'satisfiable',hyps:[atMost(x('x'),n(1))]},root:Path=new Map(),tree:Tree={leaf:[]}
 const proposal=pruneOwnedRoot([1,2,3],{tree,root},(_kept,p)=>p)
 expect(proposal.kept).toHaveLength(0);expect(check(goal,proposal.proof.tree,proposal.proof.root)).toBe(false)
})
test('deadline prevents proposals and input lists are not mutated',()=>{
 const input=[1,2,3];let calls=0;const result=pruneOwnedRoot(input,1,()=>{calls++;return 2},()=>false)
 expect(result.kept).toEqual(input);expect(result.proof).toBe(1);expect(calls).toBe(0);expect(input).toEqual([1,2,3])
})

test('owned deferral is default-off and requires both composition ownership flags',()=>{
 expect(deferOwnedReplacementChecks({})).toBe(false)
 expect(deferOwnedReplacementChecks({deferOwnedReplacementLemmas:true})).toBe(false)
 expect(deferOwnedReplacementChecks({deferOwnedReplacementLemmas:true,deferToComposition:true})).toBe(false)
 expect(deferOwnedReplacementChecks({deferOwnedReplacementLemmas:true,deferIntermediateChecks:true})).toBe(false)
 expect(deferOwnedReplacementChecks({deferOwnedReplacementLemmas:true,deferToComposition:true,deferIntermediateChecks:true})).toBe(true)
 expect(deferOwnedReplacementChecks({batchOwnedReplacementPruning:true,deferToComposition:true,deferIntermediateChecks:true})).toBe(false)
})
