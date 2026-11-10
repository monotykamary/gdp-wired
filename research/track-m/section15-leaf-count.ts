// Research-only exact count of the same Boolean guard tree guardCases visits.
import {type C} from '../../core/machine.ts'
import {type Path,truth,linear,canon} from '../../kernel/kernel.ts'
import {sub} from '../../core/solver.ts'
import {checkWall} from '../../core/wall.ts'
export function guardLeafCount(guard:C,conditions:C[],root:Path):number{
 const visit=(i:number,path:Path):number=>{
  checkWall('guard leaf planning')
  if(truth(guard,path)!==undefined)return 1
  if(i===conditions.length)return 0
  const c=conditions[i]!;if(c.op!=='<=')return 0
  if(truth(c,path)!==undefined)return visit(i+1,path)
  const a=linear(c.a,path),b=linear(c.b,path);if(!a||!b)return 0
  const lin=sub(a,b),key=canon(lin)
  return visit(i+1,new Map(path).set(key,{lin,holds:false}))+visit(i+1,new Map(path).set(key,{lin,holds:true}))
 }
 return Math.max(1,visit(0,new Map(root)))
}
