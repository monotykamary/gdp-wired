import {expect,test} from 'bun:test'
import {atMost,ite,n,x} from '../../core/machine.ts'
import {canon,check,type Path,type Tree} from '../../kernel/kernel.ts'
import {clock,grow,rowsAt} from '../../kernel/prove.ts'
import {pruneForcedCuts,rebasePath} from './rebase-path.ts'
const root:Path=new Map(),split={x:1},pinned:Path=new Map([[canon(split),{lin:split,holds:true}]])
test('path reindexing removes a redundant numeric assumption without searching',()=>{
 const g={name:'direct contradiction',hyps:[atMost(n(1),n(0))]},rows=rowsAt(g,pinned),index=rows.findIndex(r=>r.lin['1']===1&&Object.keys(r.lin).length===1),tree:Tree={leaf:[{kind:'input',index}]}
 expect(check(g,tree,pinned)).toBe(true)
 const shorter=rebasePath(g,tree,pinned,root,clock()+1000)
 expect(shorter).toBeDefined();if(shorter)expect(check(g,shorter)).toBe(true)
})
test('path reindexing keeps a split needed to expose a conditional row',()=>{
 const g={name:'conditional contradiction',hyps:[atMost(x('x'),n(0)),atMost(ite(atMost(x('x'),n(0)),n(1),n(0)),n(0))]},rows=rowsAt(g,pinned),index=rows.findIndex(r=>r.lin['1']===1&&Object.keys(r.lin).length===1),tree:Tree={leaf:[{kind:'input',index}]}
 expect(check(g,tree,pinned)).toBe(true)
 expect(rebasePath(g,tree,pinned,root,clock()+1000)).toBeUndefined()
})
test('a reindexed proposal is not a certificate without the final check',()=>{
 const g={name:'possible',hyps:[atMost(x('x'),n(1))]},proposal=rebasePath(g,{leaf:[]},pinned,root,clock()+1000)
 expect(proposal).toBeDefined();if(proposal)expect(check(g,proposal)).toBe(false)
 expect(rebasePath(g,{leaf:[]},pinned,root,clock()-1)).toBeUndefined()
})
test('derived cuts are removed only when the retained branch works without them',()=>{
 for(const conditional of [false,true]){
  const g={name:'forced cut',hyps:conditional?[atMost(x('x'),n(0)),atMost(ite(atMost(x('x'),n(0)),n(1),n(0)),n(0))]:[atMost(n(1),n(0))]},opposite:Path=new Map([[canon(split),{lin:split,holds:false}]])
  const yes=grow(g,pinned,{nodes:0,until:clock()+1000}),no=grow(g,opposite,{nodes:0,until:clock()+1000})
  expect('tree'in yes&&'tree'in no).toBe(true)
  if(!('tree'in yes)||!('tree'in no))continue
  const cut={split,no:no.tree},pruned=pruneForcedCuts(g,yes.tree,root,[cut],clock()+1000)
  expect(pruned.removed).toBe(conditional?0:1)
  expect(check(g,pruned.tree,root)).toBe(true)
  const expired=pruneForcedCuts(g,yes.tree,root,[cut],clock()-1)
  expect(expired.removed).toBe(0);expect(check(g,expired.tree,root)).toBe(true)
 }
})
