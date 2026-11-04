// A count lemma's arithmetic arm guides a cut; its complementary branch remains mandatory.
import {sub} from '../../core/solver.ts'
import {canon,linear,type Goal,type Path} from '../../kernel/kernel.ts'
import type {Cut} from './guided-split.ts'
export function lemmaCuts(goal:Goal,indices:number[],tail:Cut){
  if(indices.length>8||new Set(indices).size!==indices.length)throw Error('invalid lemma cut list')
  const cuts=indices.map(index=>{
    const row=goal.hyps[index],arm=row?.op==='or'?row.xs[0]:undefined
    if(!Number.isInteger(index)||!arm||arm.op!=='<=')throw Error('not an arithmetic lemma arm')
    const a=linear(arm.a,new Map()),b=linear(arm.b,new Map());if(!a||!b)throw Error('nonlinear cut')
    return {index,split:sub(a,b)}
  })
  let hint=tail
  for(const cut of [...cuts].reverse())hint={split:cut.split,yes:hint}
  return {hint,cuts,focusIndex:(path:Path,fallback:number)=>cuts.find(c=>path.get(canon(c.split))?.holds===false)?.index??fallback}
}
