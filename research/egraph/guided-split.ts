// Search guidance only: every cut has both branches in the returned kernel tree.
import type {C} from '../../core/machine.ts'
import type {Lin} from '../../core/solver.ts'
import {canon,type Goal,type Path} from '../../kernel/kernel.ts'
import type {Outcome} from '../../kernel/prove.ts'
// Read only a positive action equality; never mistake a negated/disjunctive guard.
export function decisionAction(condition:C|undefined):number{
  const values:number[]=[];let visited=0
  const visit=(c:C):void=>{
    if(++visited>256)throw Error('guard traversal cap')
    if(c.op==='and'){c.xs.forEach(visit);return}
    if(c.op!=='=')return
    for(const [a,b]of [[c.a,c.b],[c.b,c.a]])if(a?.op==='var'&&a.name==='op'&&b?.op==='const')values.push(b.value)
  }
  if(condition)visit(condition)
  if(values.length!==1)throw Error('ambiguous decision action')
  return values[0]!
}
export type Cut={split:Lin,yes?:Cut,no?:Cut}
export function guidedSplit(goal:Goal,hint:Cut,ask:(goal:Goal,path:Path)=>Outcome):Outcome{
  let cuts=0
  const visit=(cut:Cut|undefined,path:Path):Outcome=>{
    if(!cut)return ask(goal,path)
    if(++cuts>32)throw Error('cut cap')
    const id=canon(cut.split);if(path.has(id)||Object.keys(cut.split).every(k=>k==='1'))throw Error('invalid repeated or constant cut')
    const no=visit(cut.no,new Map(path).set(id,{lin:cut.split,holds:false}));if(!('tree'in no))return no
    const yes=visit(cut.yes,new Map(path).set(id,{lin:cut.split,holds:true}));if(!('tree'in yes))return yes
    return {tree:{split:cut.split,no:no.tree,yes:yes.tree},nodes:no.nodes+yes.nodes+1}
  }
  return visit(hint,new Map())
}
