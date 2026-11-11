// Generic marked-load STEP proposer. Every premise comes from structural
// discovery in the caller's family; no saved certificate or named law is used.
import {type E,type Law,type Machine,all,atMost,get,n,not,same,x} from './machine.ts'
import {countsForReads} from './count-facts.ts'
import {ownCountLawInstance,fixedCountFrameCase} from './count-frames.ts'
import {deferIntermediateCountChecks,type CountRequestBuilder,type CountStrategyProof,type CountStrategyOptions} from './count-strategy.ts'
import {discoverLiftedCountGuard} from './count-lifted-shape.ts'
import {discoverCountRowLoad} from './count-load-shape.ts'
import {proposeLiftedTransports} from './count-lifted-transports.ts'
import {type CountCert,type CountInst,type FrameCut,type Goal,type Instances,type LinCut,type Path,type Tree,canon,check,checkMC,countedObligations,frameOk,framePath,linear,mcGoal} from '../kernel/kernel.ts'
import {add,k,scale,solve,sub} from './solver.ts'
import {growCdcl} from '../kernel/cdcl.ts'
import {clock,fullRate,fullWork,late,rowsAt,withDeadline} from '../kernel/prove.ts'
import {countGuardTree} from './count-guard-tree.ts'
import {inlineFrozenGuard} from './count-frozen-guard.ts'
import {rebasePath} from './count-rebase-path.ts'
import {replayLinearSkeleton} from './count-replay-skeleton.ts'
import {checkedReversePrefix,UnwrittenCountPrefix} from './count-unwritten-prefix.ts'
import {copyQueryContext} from './count-query-context.ts'
import {stabilizeGuardedTree} from './count-stabilize-tree.ts'
const json=(value:unknown)=>JSON.stringify(value)
export function proveLiftedCountLoad(m:Machine,family:Law[],law:Law,until:number,requestFor:CountRequestBuilder,observe?:(event:Record<string,unknown>)=>void,options:CountStrategyOptions={}):CountStrategyProof|undefined{
 if(!family.includes(law))return
 return withDeadline(until,()=>{
  const deferred=deferIntermediateCountChecks(options),accepts=(...args:Parameters<typeof check>)=>deferred||check(...args)
  const shape=discoverLiftedCountGuard(m,law,family),choice=fixedCountFrameCase(m),load=shape&&choice&&discoverCountRowLoad(m,shape,family,choice)
  if(!shape||!choice||!load||!m.pre||late(until))return
  const stopped={},decline=(reason:string):never=>{observe?.({stage:'load-decline',reason});throw stopped}
  try{
   const a=x(law.forall!+'#'),b=x(law.keys![0]!),written=x(load.written),endpoints=[a,b,written]
   const instances:Instances=ownCountLawInstance(law,{})
   for(const premise of load.phaseLaws)instances[premise.name]=endpoints
   const packet=()=>countedObligations(m,family,{[law.name]:instances},family.indexOf(law)).at(-1)!
   const bootstrap=packet(),reads=requestFor(bootstrap.goal,bootstrap.decls).reads,maps=new Set(shape.countMaps),post=reads.filter(read=>read[1].endsWith('#')&&maps.has(read[1].slice(0,-1)))
   const rowName=shape.origin.rowCount,twins=new Set(shape.origin.twins.map(t=>t.row)),disabled=shape.countMaps.filter(map=>map!==rowName&&!twins.has(map))
   if(disabled.length!==1)return decline('disabled-count')
   const voteName=disabled[0]!,transport=proposeLiftedTransports(m,family,law,choice.value)
   const loaded=transport?.filter(region=>region.name==='load-both'||region.name.endsWith('-marked')),neither=transport?.find(region=>region.name==='load-neither')
   if(!loaded?.length||!neither)return decline('transport-plan')
   const key=(read:{post:readonly unknown[]})=>json(read.post.slice(1))
   const zeros=loaded[0]!.relations.filter(relation=>relation.kind==='zero'&&twins.has(relation.post[1].slice(0,-1))&&loaded.every(region=>region.relations.some(other=>other.kind==='zero'&&key(other)===key(relation))))
   const subsets=neither.relations.filter(relation=>relation.kind==='upper'&&relation.post[1]===voteName+'#'&&relation.target?.[1]===rowName+'#'&&json(relation.post[2])===json(relation.target[2]))
   if(!zeros.length||subsets.length!==2)return decline('transport-coverage')
   observe?.({stage:'load-match',zeroRelations:zeros.length,subsetRelations:subsets.length,regions:transport!.length})
   const find=(map:string,key:E)=>reads.find(read=>read[1]===map&&json(read[2])===json(key))?.[0]??decline('missing-count-read')
   const counts0=countsForReads(bootstrap.decls,reads),bound=counts0?.find(count=>count.v===find(rowName+'#',a))?.below
   if(!bound)return decline('row-bound')
   let prefixName='markedLoad$';const scope=json([m,family,reads]);while(scope.includes(prefixName))prefixName='$'+prefixName
   const insts:CountInst[]=[],loadWitnesses:string[]=[]
   const put=(terms:[number,string][],isLoad=false)=>{const wit=prefixName+insts.length;insts.push({wit,below:bound,terms,unit:0});if(isLoad)loadWitnesses.push(wit)}
   for(const relation of subsets)put([[1,find(relation.post[1],relation.post[2])],[-1,find(relation.target![1],relation.target![2])]])
   for(const relation of zeros)put([[1,find(relation.post[1],relation.post[2])]],true)
   instances[load.law.name]=loadWitnesses.flatMap(wit=>[a,x(wit),b,x(wit)])
   const step=packet(),again=requestFor(step.goal,step.decls)
   if(json(reads)!==json(again.reads))return decline('read-layout-drift')
   const request={reads,insts,picks:[]},goal=mcGoal(step.goal.hyps,step.decls,request),counts=countsForReads(step.decls,reads)
   if(!goal||!counts)return decline('encoding')
   const frames:FrameCut[]=[],lins:LinCut[]=[],prefix=new UnwrittenCountPrefix(step.decls,reads,[same(x(choice.name),n(choice.value)),m.pre],written,bound,'cdcl')
   const prefixFact=(postId:string,preId:string,rows:E[],sign:1|-1)=>{
    if(late(until))return
    const positive=sign===1?postId:preId,negative=sign===1?preId:postId,opposite=lins.find(cut=>cut.pos.length===1&&cut.neg.length===1&&cut.pos[0]![0]===1&&cut.neg[0]![0]===1&&cut.pos[0]![1]===negative&&cut.neg[0]![1]===positive)
    return opposite&&checkedReversePrefix(counts,opposite)||prefix.prove(postId,preId,rows,sign,until)
   }
   for(const endpoint of [a,b])for(const sign of [1,-1] as const){const cut=prefixFact(find(rowName+'#',endpoint),find(rowName,endpoint),[endpoint],sign);if(cut)lins.push(cut)}
   for(const endpoint of [a,b]){const cut=prefixFact(find(voteName+'#',endpoint),find(voteName,endpoint),[endpoint],1);if(cut)lins.push(cut)}
   const reused=new Map<string,{tree:Tree,path:Path,goal:Goal}>(),roots=new Map<Tree,Path>()
   const ask=(path:Path,stage:string,frame=false):Tree|undefined=>{
    if(late(until))return
    if(stage==='neither-written')for(const [postId,map,key]of post){
     if(map===rowName+'#')continue
     const rows=key.op==='add'&&key.a.op==='mul'?[key.a.a,key.b]:[key]
     for(const sign of map===voteName+'#'?[1] as const:[1,-1] as const){const cut=prefixFact(postId,find(map.slice(0,-1),key),rows,sign);if(cut&&!lins.some(old=>json(old)===json(cut)))lins.push(cut)}
    }
    if(frame)for(const [postId,map,key]of post){
     const pre=reads.find(read=>read[1]===map.slice(0,-1)&&json(read[2])===json(key))
     if(pre){const cut={post:postId,pre:pre[0],when:[...path.values()].map(atom=>atom.holds?atom.lin:add(scale(atom.lin,-1),k(1)))};if(frameOk(counts,cut))frames.push(cut)}
    }
    const root=framePath(frames,[],path,[],lins),before=fullWork(),deadline=Math.min(until,clock()+500),remember=(tree:Tree)=>{roots.set(tree,new Map(root));return tree}
    const direct=solve(rowsAt(goal,root),500)
    if(direct.kind==='refuted')return remember({leaf:direct.steps})
    const cached=reused.get(stage)
    if(cached){const end=Math.min(deadline,clock()+25),tree=rebasePath(cached.goal,cached.tree,cached.path,root,end,goal)??replayLinearSkeleton(goal,cached.tree,root,end,{deferCheck:deferred});if(tree&&accepts(goal,tree,root))return remember(tree)}
    const selected=stage==='both-written'||stage.endsWith('-loaded')?insts.filter(inst=>inst.terms.length===1):stage.endsWith('-empty')?insts.filter(inst=>inst.terms.length===2&&inst.terms[0]![1]===find(voteName+'#',stage.startsWith('a-written')?b:a)):[]
    let searchRoot=root
    if(stage.endsWith('-loaded')){
     const other=stage.startsWith('a-written')?b:a,order=sub(linear(other,path)!,linear(written,path)!),drop=new Set([canon(order),canon(scale(order,-1))])
     searchRoot=framePath(frames,[],new Map([...path].filter(([,atom])=>!drop.has(canon(atom.lin)))),[],lins)
    }
    const hyps=copyQueryContext(step.goal.hyps,searchRoot,counts,insts,selected),view=mcGoal(hyps,step.decls,{...request,insts:selected})
    if(!view)return
    const result=growCdcl(view,searchRoot,{nodes:0,until:deadline}),candidate='tree'in result?(rebasePath(view,result.tree,searchRoot,searchRoot,deadline,goal)??replayLinearSkeleton(goal,result.tree,searchRoot,deadline)):undefined
    const general=candidate&&accepts(goal,candidate,searchRoot)?candidate:undefined,lift=general&&(searchRoot===root?general:rebasePath(goal,general,searchRoot,root,deadline,goal)??replayLinearSkeleton(goal,general,root,deadline,{deferCheck:deferred}))
    observe?.({stage,checked:!!lift,units:(fullWork()-before)/fullRate,...(!('tree'in result)?{outcome:result.stuck,witness:result.witness}:{})})
    if(general&&!reused.has(stage))reused.set(stage,{tree:general,path:searchRoot,goal})
    return lift&&accepts(goal,lift,root)&&!late(until)?remember(lift):undefined
   }
   const split=countGuardTree(until,{yesFirst:true}),marked=(row:E,path:Path,stage:string)=>split.condition(atMost(n(load.marker.value),get(load.marker.map,row)),path,p=>ask(p,stage+'-loaded'),p=>ask(p,stage+'-empty',true))
   const regions=(path:Path)=>split.condition(same(a,written),path,p=>split.condition(same(b,written),p,q=>ask(q,'both-written'),q=>marked(b,q,'a-written')),p=>split.condition(same(b,written),p,q=>marked(a,q,'b-written'),q=>ask(q,'neither-written',true)))
   const domain=all(m.pre,...endpoints.flatMap(row=>[{op:'<' as const,a:row,b:bound},atMost(row,n(shape.origin.width-1))])),active=inlineFrozenGuard(m.step.flags??{},load.guard)
   const inactive=(path:Path)=>split.condition(all(...choice.values.filter(value=>value!==choice.value).map(value=>not(same(x(choice.name),n(value))))),path,p=>ask(p,'inactive',true),p=>ask(p,'inactive-operation-contradiction'))
   const tree=split.condition(domain,new Map(),path=>split.condition(active,path,regions,inactive),path=>ask(path,'outside-domain'))
   if(!tree)return decline('tree')
   const stable=stabilizeGuardedTree(goal,tree,frames,lins,roots,until,{deferCheck:deferred})
   observe?.({stage:'load-stabilize',completed:!!stable.tree,rebased:stable.rebased,failed:stable.failed,phasePremises:load.phaseLaws.length})
   if(!stable.tree||late(until))return
   const cert:CountCert={...request,frames,lins,tree:stable.tree}
   return (options.deferToComposition||checkMC(step.goal.hyps,step.decls,cert))&&!late(until)?{instances,certs:{[step.goal.name]:cert},...(deferred?{status:'unchecked' as const}:{})}:undefined
  }catch(error){if(error===stopped)return;throw error}
 })
}
