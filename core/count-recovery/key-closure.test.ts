import {expect,test} from 'bun:test'
import {atMost,get,minus,n,plus,same,times,x} from '../machine.ts'
import {canon,check,type Path,type Tree} from '../../kernel/kernel.ts'
import {clock,grow} from '../../kernel/prove.ts'
import {closeKeyReads} from './key-closure.ts'
for(const correct of [true,false])test(`read-key closure ${correct?'checks the packed subtraction guard':'does not equate a wrong offset'}`,()=>{
 const row=x('row'),source=x('source'),w=x('w'),ordered={source:1,row:-1},root:Path=new Map([[canon(ordered),{lin:ordered,holds:true}]])
 const shift=times(64,correct?minus(row,source):plus(minus(row,source),n(1))),key=minus(plus(times(64,row),w),shift),original=plus(times(64,source),w)
 const g={name:'read-key closure',hyps:[atMost(source,row),same(get('Cells',key),n(1)),same(get('Cells',original),n(0))]},until=clock()+1000
 const closed=closeKeyReads(g,root,[{map:'Cells',key},{map:'Cells',key:original}],new Set(['w']),until),out=grow(g,closed.path,{nodes:0,until,units:true})
 let tree:Tree|undefined='tree'in out?out.tree:undefined
 if(tree)for(const cut of [...closed.cuts].reverse())tree={split:cut.split,yes:tree,no:cut.no}
 if(correct){expect(closed.cuts.length).toBeGreaterThan(0);expect(tree).toBeDefined();if(tree)expect(check(g,tree,root)).toBe(true)}else expect(tree).toBeUndefined()
})
