// Dependency slicing only: do not rewrite terms or hypotheses. A condition
// established by the caller's checked path need not keep its inactive branches
// alive, but all returned proof trees still check against the original goal.
import {type C} from '../../core/machine.ts'
import {type Path,truth} from '../../kernel/kernel.ts'
// Expose conjunctions hidden behind phase implications before dependency
// filtering. The actual terms are retained, so row transport need not invent
// identities between rewritten conditional-expression columns.
export function piecesAt(c:C,path:Path,neg=false):C[]{
 const t=truth(c,path)
 if(t!==undefined)return t!==neg?[]:[{op:'or',xs:[]}]
 if(c.op==='not')return piecesAt(c.x,path,!neg)
 if(c.op==='and'&&!neg||c.op==='or'&&neg)return c.xs.flatMap(x=>piecesAt(x,path,neg))
 if(c.op==='and'||c.op==='or'){
  const open=c.xs.filter(x=>truth(x,path)===undefined)
  if(open.length===1)return piecesAt(open[0]!,path,neg)
 }
 return [neg?{op:'not',x:c}:c]
}
export function walkLive(root:unknown,path:Path,visit:(value:any)=>void):void{
 const seen=new WeakSet<object>()
 const go=(value:any):void=>{
  if(!value||typeof value!=='object'||seen.has(value))return
  seen.add(value)
  if(['not','and','or','<','<=','='].includes(value.op)&&truth(value as C,path)!==undefined)return
  if(value.op==='if'){
   const chosen=truth(value.c,path)
   if(chosen!==undefined){go(chosen?value.then:value.else);return}
  }
  visit(value)
  for(const child of Array.isArray(value)?value:Object.values(value))go(child)
 }
 go(root)
}
