// A count-free live conclusion should not pay for unrelated count instances.
// Every projection is weakening-only, and every tree is transported to g.
import {type C,type Machine,walkOnce} from '../machine.ts'
import {type CountCert,type Goal,type Path,type Tree,canon,linear,truth} from '../../kernel/kernel.ts'
import {sub} from '../solver.ts'
import {clock,grow,widen,withDeadline} from '../../kernel/prove.ts'
import {modelSequence} from '../../kernel/model-sequence.ts'
import {REFUTED} from '../../kernel/cdcl.ts'
import {fieldOnlyGoal} from './field-only.ts'
import {foldPath} from './fold-path.ts'
import {booleanCore,walkChoices} from './boolean-core.ts'
export function fieldDirection(claim:C|undefined,path:Path):Record<string,number>|undefined{
 let direction:Record<string,number>|undefined
 walkChoices(claim,path,(read:any)=>{
  if(read.op!=='get')return
  walkOnce(read.key,(o:any)=>{
   if(direction||o.op!=='sub'||o.a.op!=='var'||o.b.op!=='var'||truth({op:'<=',a:o.a,b:o.b},path)!==undefined)return
   const a=linear(o.a,path),b=linear(o.b,path);if(a&&b)direction=sub(a,b)
  })
 })
 return direction
}
export function fieldCase(m:Machine,g:Goal,cert:Pick<CountCert,'reads'|'insts'>,claim:C|undefined,path:Path,until:number,trace?:(e:Record<string,unknown>)=>void,naturalDepth=0):Tree|undefined{
 const field=fieldOnlyGoal(g,m,cert,claim,path)
 if(!field||clock()>=until)return undefined
 const began=clock()
 // Expose a scalar direction before natural subtraction makes copied read
 // keys opaque. Both source paths are proved; no direction is assumed.
 const folded=foldPath(field,path),query=modelSequence(path)(folded.goal,until)
 if(!('tree'in query)&&query.stuck==='sat'){
  trace?.({stage:'field-case',hyps:field.hyps.length,ms:Math.round(clock()-began),proposed:false,outcome:query.stuck,model:query.witness})
  return undefined
 }
 const reduced=!('tree'in query)&&query.why===REFUTED&&query.core?.length?{...folded.goal,hyps:query.core.map(i=>folded.goal.hyps[i]!)}:folded.goal
 const direction=naturalDepth<2&&!('tree'in query)&&query.why===REFUTED?fieldDirection({op:'and',xs:reduced.hyps},path):undefined
 if(direction){
  const id=canon(direction),yes=fieldCase(m,g,cert,claim,new Map(path).set(id,{lin:direction,holds:true}),until,trace,naturalDepth+1)
  const no=yes&&fieldCase(m,g,cert,claim,new Map(path).set(id,{lin:direction,holds:false}),until,trace,naturalDepth+1)
  const tree=yes&&no?{split:direction,yes,no}:undefined
  trace?.({stage:'field-natural-direction',ms:Math.round(clock()-began),proposed:!!tree})
  return tree
 }
 const keys=new Set<string>();let packed=false
 if(!('tree'in query)&&query.why===REFUTED&&query.core?.length&&query.core.length<=8)walkOnce(reduced.hyps,(o:any)=>{
  if(o.op!=='get'||['var','const'].includes(o.key.op))return
  packed=true;walkOnce(o.key,(k:any)=>{if(k.op==='var'&&!m.inputs.includes(k.name)&&!m.params.includes(k.name)&&!(k.name in m.state))keys.add(k.name)})
 })
 const events:object[]=[],point=packed?booleanCore(reduced,path,keys,until,events,{extended:true,scalarGuards:true,deferCheck:true}):undefined
 for(const event of events)trace?.(event as Record<string,unknown>)
 const out=point?{tree:point}:'tree'in query?query:grow(reduced,path,{nodes:0,until,units:true})
 const expanded='tree'in out?withDeadline(until,()=>widen(reduced,folded.goal,out.tree,{},path,path)):undefined
 const lifted=expanded&&withDeadline(until,()=>widen(folded.goal,field,expanded,folded.opaque,path,path))
 const tree=lifted&&withDeadline(until,()=>widen(field,g,lifted,{},path,path))
 trace?.({stage:'field-case',hyps:field.hyps.length,core:query.core?.length,ms:Math.round(clock()-began),proposed:!!tree,outcome:'tree'in query?'tree':query.stuck,...(!('tree'in query)&&query.stuck==='sat'?{model:query.witness}:{})})
 return tree
}
