// Conditional threshold-increment STEP proposal. Role discovery and the
// family's no-quorum premise select witnesses; only the native checker accepts.
import {type C,type E,type Law,type Machine,all,atMost,get,less,n,plus,times,walkOnce,x} from './machine.ts'
import {type CountCert,type CountInst,type FrameCut,type Path,type Tree,checkMC,countedObligations,frameOk,framePath,mcGoal} from '../kernel/kernel.ts'
import {type CountRequestBuilder,type CountStrategyOptions,type CountStrategyProof} from './count-strategy.ts'
import {discoverLiftedCountGuard,discoverLiftedCountOperation} from './count-lifted-shape.ts'
import {discoverCountGuardShape} from './count-guard-shape.ts'
import {discoverLiftedCountPrerequisites} from './count-lifted-prerequisite.ts'
import {countFrameConditions,fixedCountFrameCase,ownCountLawInstance} from './count-frames.ts'
import {countsForReads} from './count-facts.ts'
import {matchLiftedCountBodies} from './count-lifted-transports.ts'
import {clock,fullRate,fullWork,late,withDeadline} from '../kernel/prove.ts'
import {growCdcl} from '../kernel/cdcl.ts'
import {add,k,scale} from './solver.ts'
import {countGuardTree} from './count-guard-tree.ts'
import {inlineFrozenGuard} from './count-frozen-guard.ts'
import {minimalTransportView,minimalViewFirst} from './count-minimal-view.ts'
import {copyQueryContext} from './count-query-context.ts'
import {stabilizeGuardedTree} from './count-stabilize-tree.ts'
const json=(value:unknown)=>JSON.stringify(value)
export function proveLiftedCountIncrement(m:Machine,family:Law[],law:Law,until:number,requestFor:CountRequestBuilder,observe?:(event:Record<string,unknown>)=>void,options:CountStrategyOptions={}):CountStrategyProof|undefined{
 if(!family.includes(law))return
 return withDeadline(until,()=>{
  const shape=discoverLiftedCountGuard(m,law,family),choice=fixedCountFrameCase(m),operation=shape&&choice&&discoverLiftedCountOperation(m,shape,choice.value)
  if(!shape||!choice||operation?.kind!=='threshold-increment'||!('write'in operation)||!m.pre||late(until)){observe?.({stage:'increment-decline',reason:'shape-or-operation'});return}
  const write=operation.write
  if(write.increment!==1){observe?.({stage:'increment-decline',reason:'nonincrement-write'});return}
  const stopped={},decline=(reason:string):never=>{observe?.({stage:'increment-decline',reason});throw stopped}
  try{
   const lower=discoverLiftedCountPrerequisites(m,law,family).flatMap(prerequisite=>{
    const found=discoverCountGuardShape(m,prerequisite.law,family)
    if(!found||found.rowMap!==shape.origin.rowCount||found.memberField!==shape.countShape.memberField||found.thresholdField!==shape.countShape.thresholdField)return []
    return [{law:prerequisite.law,shape:found}]
   })
   if(lower.length!==1)return decline('no-unique-guarded-vote-premise')
   const premise=lower[0]!,twins=new Set(shape.origin.twins.map(twin=>twin.row)),votes=shape.countMaps.filter(map=>map!==shape.origin.rowCount&&!twins.has(map))
   if(votes.length!==1)return decline('disabled-count')
   const vote=votes[0]!,a=x(law.forall!+'#'),b=x(law.keys![0]!),actor=x(write.source),rowMap=shape.origin.rowCount
   let prefix='increment$';const scope=json([m,family]);while(scope.includes(prefix))prefix='$'+prefix
   const labels=Array.from({length:7},(_,index)=>prefix+'w'+index),instances=ownCountLawInstance(law,{[premise.law.name]:[actor,a,actor,b]})
   for(const [name,flag]of Object.entries(m.step.flags??{}))if(flag.op==='all')instances['?'+name]=labels.map(x)
   const step=countedObligations(m,family,{[law.name]:instances},family.indexOf(law)).at(-1)!,reads=[...requestFor(step.goal,step.decls).reads]
   const bind=(map:string,key:E)=>{const old=reads.find(read=>read[1]===map&&json(read[2])===json(key));if(old)return old[0];const id=prefix+'r'+reads.length;reads.push([id,map,key]);return id}
   const pair=(left:E,right:E)=>plus(times(shape.origin.width,left),right)
   const row=countsForReads(step.decls,[[prefix+'row',rowMap,actor]])?.[0],used=new Set<string>()
   walkOnce([m.pre,m.assume,m.step.flags?.[write.guard]],(node:any)=>{if(node.op==='get')used.add(node.map)})
   const aliases=Object.entries(m.counts??{}).filter(([map,definition])=>!definition.base&&used.has(map)).flatMap(([map])=>{const count=countsForReads(step.decls,[[prefix+'alias',map,n(0)]])?.[0];return row&&count&&matchLiftedCountBodies(row,count)?[map]:[]})
   if(aliases.length!==1)return decline('no-unique-actor-row-count')
   const S=bind(write.inputCount,n(0)),X=bind(aliases[0]!,n(0)),R=bind(rowMap,actor),V=bind(vote,actor),TA=bind(premise.shape.voteMap,pair(actor,a)),TB=bind(premise.shape.voteMap,pair(actor,b))
   const beforeA=bind(vote,a),beforeB=bind(vote,b),afterA=bind(vote+'#',a),afterB=bind(vote+'#',b),counts=countsForReads(step.decls,reads),bound=counts?.find(count=>count.v===S)?.below
   if(!counts||!bound)return decline('count-reads')
   const vectors:[number,string][][]=[[[1,X],[-1,R]],[[1,R],[-1,X]],[[1,S],[-1,V]],[[1,S],[-1,TA]],[[1,S],[-1,TB]],[[1,afterA],[-1,beforeA]],[[1,afterB],[-1,beforeB]]]
   const insts:CountInst[]=vectors.map((terms,index)=>({wit:labels[index]!,below:bound,terms,unit:0})),request={reads,insts,picks:[]},goal=mcGoal(step.goal.hyps,step.decls,request)
   if(!goal)return decline('encoding')
   const frames:FrameCut[]=[],roots=new Map<Tree,Path>()
   observe?.({stage:'increment-premise',premise:premise.law.name,rowAlias:aliases[0],instances:insts.length})
   const ask=(path:Path,stage:string,index?:number):Tree|undefined=>{
    if(late(until))return
    const root=framePath(frames,[],path),started=fullWork(),end=Math.min(until,clock()+500)
    const minimal=index===undefined?{goal:mcGoal(copyQueryContext(step.goal.hyps,root,counts,insts,[]),step.decls,{reads,insts:[],picks:[]}),path:root}:minimalTransportView(step.goal.hyps,step.decls,reads,insts,[insts[index]!],root)
    if(!minimal?.goal)return
    const result=minimalViewFirst(goal,minimal.goal,root,end,growCdcl,minimal.path),tree=result.tree
    observe?.({stage,index,checked:!!tree,hyps:minimal.goal.hyps.length,leafCap:late(end),units:(fullWork()-started)/fullRate,minimal:result.minimalKind,fullFallback:result.fallback,minimalUnits:result.minimalUnits,fallbackUnits:result.fallbackUnits,...(result.witness?{witness:result.witness}:{})})
    if(!tree||late(end))return
    roots.set(tree,new Map(root));return tree
   }
   const frame=(path:Path,every=false)=>{for(const read of reads.filter(read=>read[1].endsWith('#')&&(every||read[1]!==vote+'#'))){const before=reads.find(old=>old[1]===read[1].slice(0,-1)&&json(old[2])===json(read[2]));if(!before)continue;const cut={post:read[0],pre:before[0],when:[...path.values()].map(atom=>atom.holds?atom.lin:add(scale(atom.lin,-1),k(1)))};if(frameOk(counts,cut))frames.push(cut)}}
   const split=countGuardTree(until,{yesFirst:true}),factRow=(index:number)=>add(...insts[index]!.terms.map(([coefficient,id])=>({[id]:coefficient})))
   const fact=(index:number,path:Path,next:(path:Path)=>Tree|undefined):Tree|undefined=>split.rows([factRow(index)],path,next,branch=>ask(branch,'count-fact',index))
   const finish=(path:Path)=>split.condition({op:'=',a,b:actor},path,left=>fact(2,left,p=>split.condition({op:'=',a:b,b:actor},p,q=>ask(q,'both-actor'),q=>fact(6,q,r=>ask(r,'left-actor')))),left=>fact(5,left,p=>split.condition({op:'=',a:b,b:actor},p,q=>fact(2,q,r=>ask(r,'right-actor')),q=>fact(6,q,r=>ask(r,'neither-actor')))))
   const term=(row:E,index:number,path:Path,next:(path:Path)=>Tree|undefined)=>split.condition(atMost(get(shape.countShape.thresholdField,row),get(shape.countShape.memberField,actor)),path,next,branch=>fact(index,branch,p=>ask(p,'term-contradiction')))
   const domain:C=all(...[a,b,actor].flatMap(row=>[less(row,bound),less(row,n(shape.origin.width))])),active=inlineFrozenGuard(m.step.flags??{},write.guard)
   const run=(path:Path)=>split.rows(countFrameConditions(choice),path,p=>split.condition(domain,p,q=>{frame(q);return split.condition(active,q,r=>fact(0,r,s=>fact(1,s,t=>term(a,3,t,u=>term(b,4,u,finish)))),r=>{frame(r,true);return ask(r,'inactive')})},q=>ask(q,'outside-domain')),p=>ask(p,'outside-operation'))
   const tree=split.condition(m.pre,new Map(),run,path=>ask(path,'outside-pre'))
   if(!tree)return decline('tree')
   const stable=stabilizeGuardedTree(goal,tree,frames,[],roots,until)
   if(!stable.tree||late(until))return decline('stabilization')
   const cert:CountCert={...request,frames,tree:stable.tree}
   return (options.deferToComposition||checkMC(step.goal.hyps,step.decls,cert))&&!late(until)?{instances,certs:{[step.goal.name]:cert}}:undefined
  }catch(error){if(error===stopped)return;throw error}
 })
}
