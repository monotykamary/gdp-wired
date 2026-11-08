// Untrusted activation case splitting. Every leaf is transported back to
// the original goal/path, and the complete split tree is checked once more.
import {type C,type Machine,plus,n} from '../machine.ts'
import {type CountCert,type CountDecl,type Goal,type Path,type Tree,canon,linear,truth} from '../../kernel/kernel.ts'
import {sub} from '../solver.ts'
import {atPoint,clock,withDeadline} from '../../kernel/prove.ts'
import {fieldBoundLemmas} from './field-bound-lemmas.ts'
import {frameLemmas} from './frame-lemmas.ts'
import {fieldCase} from './field-case.ts'
import {type SourceProofMemo} from './source-memo.ts'
import {wallTree,check,solve,grow,rowsAt,widen} from './ops.ts'
type Proposal=Pick<CountCert,'reads'|'insts'>

export const guardCases:typeof guardCasesImpl=(...args)=>wallTree('guard-case-reconstruction',()=>guardCasesImpl(...args))
function guardCasesImpl(m:Machine,ds:CountDecl[],g:Goal,cert:Proposal,guard:C,until:number,trace:object[],slot=0,root:Path=new Map(),options:{deferCheck?:boolean,claim?:C,memo?:SourceProofMemo}={}):Tree|undefined{
 const deferNested=!!options.deferCheck
 const conditions:C[]=[],booleans=true
 const collect=(c:C):boolean=>{
  if(c.op==='and'||booleans&&c.op==='or')return c.xs.every(collect)
  if(booleans&&c.op==='not')return collect(c.x)
  if(c.op==='='){conditions.push({op:'<=',a:c.a,b:c.b},{op:'<=',a:c.b,b:c.a});return true}
  if(c.op==='<='){conditions.push(c);return true}
  if(c.op==='<'){conditions.push({op:'<=',a:plus(c.a,n(1)),b:c.b});return true}
  return false
 }
 if(!collect(guard)||conditions.length>12)return undefined
 const inactiveGoal={...g,hyps:[...g.hyps.slice(0,slot),{op:'not' as const,x:guard},...g.hyps.slice(slot)]}
 let inactive:Tree|undefined,attempted=false,inactiveLeaf:{tree:Tree,path:Path}|undefined
 const leaf=(hyps:C[],path:Path,active:boolean):Tree|undefined=>{
  if(clock()>=until)return undefined
  const assumption=active?guard:{op:'and' as const,xs:hyps},sourceOnly=false,goal=sourceOnly?g:{...g,hyps:[...g.hyps.slice(0,slot),assumption,...g.hyps.slice(slot)]},start=clock(),end=active?until:Math.min(until,clock()+500)
  const cached=options.memo?.get(g,path,end)
  if(cached&&(deferNested||check(g,cached,path))){trace.push({stage:'source-memo',scope:'guard',active});return cached}
  let proof=fieldCase(m,goal,cert,options.claim,path,Math.min(end,clock()+150),e=>trace.push({...e,guardActive:active}))
  if(!proof&&!active){
   if(!attempted){attempted=true;const begun=clock();inactive=frameLemmas(inactiveGoal,cert,end,trace,root,{stopAfterFailed:2,deferCheck:deferNested});trace.push({stage:'shared-frame',ms:Math.round(clock()-begun),proved:!!inactive})}
   if(inactive){const shared=widen(inactiveGoal,g,inactive,{},root,path),accepted=!!shared&&(deferNested||check(g,shared,path));trace.push({stage:'shared-frame-lift',ms:Math.round(clock()-start),checked:accepted&&!deferNested,proposed:!!shared,deferred:deferNested});if(accepted)return shared}
  }
  if(!proof&&!active&&inactiveLeaf){
   const shared=withDeadline(Math.min(end,clock()+50),()=>widen(g,g,inactiveLeaf!.tree,{},inactiveLeaf!.path,path)),accepted=!!shared&&(deferNested||check(g,shared,path))
   trace.push({stage:'inactive-path-reuse',ms:Math.round(clock()-start),checked:accepted&&!deferNested,proposed:!!shared,deferred:deferNested})
   if(accepted)return shared
  }
  if(!proof&&!active){const simple=solve(rowsAt(goal,path),500);if(simple.kind==='refuted')proof={leaf:simple.steps}}
  if(!proof)proof=active?fieldBoundLemmas(m,ds,goal,cert,end,trace,undefined,path,{deferCheck:true,fieldClaim:options.claim,memo:options.memo}):frameLemmas(goal,cert,end,trace,path,{deferCheck:deferNested})
  if(!proof&&clock()<end){
   const before=atPoint.on;atPoint.on=false
   try{const out=grow(goal,path,{nodes:0,until:end,units:false});if('tree'in out)proof=out.tree}finally{atPoint.on=before}
  }
  // The complete guard tree below checks active proofs after source transport.
  // Avoid checking the same large active tree before and after that transport.
  const lifted=proof&&(sourceOnly?proof:widen(goal,g,proof,{},path,path)),accepted=!!lifted&&(active||deferNested||check(g,lifted,path))
  if(accepted&&lifted)options.memo?.put(g,path,lifted)
  if(!active&&accepted&&lifted&&!inactiveLeaf)inactiveLeaf={tree:lifted,path:new Map(path)}
  trace.push({stage:'guard-leaf',active,sourceOnly,hyps:hyps.length,ms:Math.round(clock()-start),checked:!active&&!deferNested&&accepted,proposed:!!proof,transported:!!lifted,deferred:active||deferNested})
  return accepted?lifted:undefined
 }
 const visit=(i:number,hyps:C[],path:Path):Tree|undefined=>{
  if(booleans){const active=truth(guard,path);if(active!==undefined)return leaf(hyps,path,active);if(i===conditions.length)return undefined}
  else if(i===conditions.length)return leaf(hyps,path,true)
  if(clock()>=until)return undefined
  const c=conditions[i]!;if(c.op!=='<=')return undefined
  const known=truth(c,path)
  if(known===true)return visit(i+1,[...hyps,c],path)
  if(known===false)return booleans?visit(i+1,[...hyps,{op:'not',x:c}],path):leaf([...hyps,{op:'not',x:c}],path,false)
  const a=linear(c.a,path),b=linear(c.b,path);if(!a||!b)return undefined
  const split=sub(a,b),id=canon(split)
  const noPath=new Map(path).set(id,{lin:split,holds:false}),no=booleans?visit(i+1,[...hyps,{op:'not',x:c}],noPath):leaf([...hyps,{op:'not',x:c}],noPath,false)
  if(!no)return undefined
  const yesPath=new Map(path).set(id,{lin:split,holds:true}),yes=visit(i+1,[...hyps,c],yesPath)
  return yes?{split,yes,no}:undefined
 }
 const tree=visit(0,[],new Map(root))
 const accepted=!!tree&&(options.deferCheck||check(g,tree,root))
 trace.push({stage:'guard-complete',cuts:conditions.length,checked:!options.deferCheck&&accepted,...(options.deferCheck?{proposed:!!tree,deferred:true}:{})})
 // Deferred trees are proposals only; the composing caller must check them.
 return accepted?tree:undefined
}
