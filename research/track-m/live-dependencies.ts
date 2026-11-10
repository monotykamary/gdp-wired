// Dependency slicing only: do not rewrite terms or hypotheses. A condition
// established by the caller's checked path need not keep its inactive branches
// alive, but all returned proof trees still check against the original goal.
import {type C} from '../../core/machine.ts'
import {type Goal,type Path,truth} from '../../kernel/kernel.ts'
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
// A proposed small core can omit a witness's source-side guard instance.
// Re-add only existing hypotheses about witnesses used by that core; never
// synthesize a guard premise or import an unrelated witness's condition.
export function sourceWitnessContext(source:Goal,core:Goal,wits:ReadonlySet<string>,path:Path):Goal{
 const active=new Set<string>()
 walkLive(core.hyps,path,o=>{if(o.op==='var'&&wits.has(o.name))active.add(o.name)})
 if(!active.size)return core
 const extra=source.hyps.filter(c=>{
  if(core.hyps.includes(c))return false
  let wanted=false,foreign=false
  walkLive(c,path,o=>{if(o.op==='var'&&wits.has(o.name)){if(active.has(o.name))wanted=true;else foreign=true}})
  return wanted&&!foreign
 })
 return extra.length?{...core,hyps:[...core.hyps,...extra]}:core
}
// Preserve source scalar domains in a small point core. A packed-row proof can
// need the original size/stride bound even when a numeric core omits it.
export function sourceScalarContext(source:Goal,core:Goal,names:ReadonlySet<string>,path:Path):Goal{
 const extra=source.hyps.flatMap(c=>piecesAt(c,path)).filter(c=>{
  if(core.hyps.includes(c))return false
  let scalar=true
  walkLive(c,path,(o:any)=>{if(o.op==='get'||o.op==='flag'||o.op==='all'||o.op==='var'&&!names.has(o.name))scalar=false})
  return scalar
 })
 return extra.length?{...core,hyps:[...core.hyps,...extra]}:core
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
