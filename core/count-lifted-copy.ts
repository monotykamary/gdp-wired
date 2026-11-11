import {FrameFactPool} from './count-emitter-frame-pool.ts'
// A row-copy STEP proposal from discovered source/target roles and the lifted
// law's own tuples. All transports are ordinary checked per-key linear facts.
import {type C,type E,type Law,type Machine,atMost,n,not,same,walkOnce,x} from './machine.ts'
import {type CountInst,type CountCert,type FrameCut,type LinCut,type Path,type Tree,check,checkMC,countedObligations,frameOk,framePath,mcGoal,substE} from '../kernel/kernel.ts'
import {deferIntermediateCountChecks,type CountRequestBuilder,type CountStrategyOptions,type CountStrategyProof} from './count-strategy.ts'
import {discoverLiftedCountGuard} from './count-lifted-shape.ts'
import {discoverCountRowCopy} from './count-copy-shape.ts'
import {proposeLiftedTransports} from './count-lifted-transports.ts'
import {countsForReads} from './count-facts.ts'
import {countFrameConditions,fixedCountFrameCase,ownCountLawInstance} from './count-frames.ts'
import {clock,fullRate,fullWork,late,rowsAt,withDeadline} from '../kernel/prove.ts'
import {growCdcl} from '../kernel/cdcl.ts'
import {add,k,scale,solve} from './solver.ts'
import {countGuardTree} from './count-guard-tree.ts'
import {inlineFrozenGuard} from './count-frozen-guard.ts'
import {guardLinearFact} from './count-guard-facts.ts'
import {rebasePath} from './count-rebase-path.ts'
import {replayLinearSkeleton} from './count-replay-skeleton.ts'
import {stabilizeGuardedTree} from './count-stabilize-tree.ts'
const json=(value:unknown)=>JSON.stringify(value)
export function proveLiftedCountCopy(m:Machine,family:Law[],law:Law,until:number,requestFor:CountRequestBuilder,observe?:(event:Record<string,unknown>)=>void,options:CountStrategyOptions={}):CountStrategyProof|undefined{
 if(!family.includes(law))return
 return withDeadline(until,()=>{
  const deferred=deferIntermediateCountChecks(options),accepts=(...args:Parameters<typeof check>)=>deferred||check(...args)
  const shape=discoverLiftedCountGuard(m,law,family),choice=fixedCountFrameCase(m),copy=shape&&choice&&discoverCountRowCopy(m,shape.countShape,choice)
  if(!shape||!choice||!copy||!m.pre||late(until))return
  const stopped={},decline=(reason:string):never=>{observe?.({stage:'copy-decline',reason});throw stopped}
  let framePool:FrameFactPool|undefined
  try{
   const from=x(copy.from),to=x(copy.to),a=x(law.forall!+'#'),b=x(law.keys![0]!),transportRegions=proposeLiftedTransports(m,family,law,choice.value)
   if(transportRegions?.length!==4)return decline('transport-plan')
   const tuples=transportRegions[0]!.tuples,instances=ownCountLawInstance(law,{})
   instances[law.name]=tuples.flat()
   const packet=(terms: E[])=>countedObligations(m,family,{[law.name]:{[law.name]:terms}},family.indexOf(law)).at(-1)!
   const step=packet(instances[law.name]!),reads=requestFor(step.goal,step.decls).reads,counts=countsForReads(step.decls,reads)
   if(!counts)return decline('counts')
   const targetMaps=new Set(shape.countMaps),postReads=reads.filter(read=>read[1].endsWith('#')&&targetMaps.has(read[1].slice(0,-1)))
   const read=(map:string,key:E)=>reads.find(r=>r[1]===map&&json(r[2])===json(key))?.[0]??decline('missing-copy-read')
   const bound=m.counts?.[shape.origin.rowCount]?.below
   if(!bound)return decline('bound')
   let prefix='rowCopy$';const scope=json([m,family,reads]);while(scope.includes(prefix))prefix='$'+prefix
   const caseInsts:CountInst[][]=transportRegions.map((region,i)=>postReads.flatMap(([post,map,key],j)=>{
    const vars=Object.fromEntries([law.forall!+'#',...law.keys!].map((name,index)=>[name,region.activeTuple[index]!])),targetKey=substE(key,{vars,maps:{},flags:{}})
    const relation=region.relations.find(relation=>relation.post[1]===map&&json(relation.post[2])===json(key)&&relation.target?.[1]===map.slice(0,-1)&&json(relation.target[2])===json(targetKey))
    if(!relation?.target||relation.kind==='zero')return decline('unmatched-copy-transport')
    const pre=read(relation.target[1],relation.target[2]),forward:CountInst={wit:prefix+i+'$'+j,below:bound,terms:[[1,post],[-1,pre]],unit:0}
    return relation.kind==='equality'?[forward,{...forward,wit:forward.wit+'$reverse',terms:[[1,pre],[-1,post]]}]:[forward]
   }))
   observe?.({stage:'copy-match',regions:transportRegions.length,tuples:tuples.length,relations:caseInsts.map(group=>group.length)})
   const unique=new Map<string,CountInst>()
   for(const group of caseInsts)for(let i=0;i<group.length;i++){const inst=group[i]!,key=json(inst.terms),old=unique.get(key);if(old)group[i]=old;else unique.set(key,inst)}
   const request={reads,insts:[],picks:[]},goal=mcGoal(step.goal.hyps,step.decls,request)
   if(!goal)return decline('encoding')
   const countMaps=new Set(step.decls.map(decl=>decl.map)),scalarHyps=step.goal.hyps.filter(hyp=>{let counted=false;walkOnce(hyp,(node:any)=>{if(node.op==='get'&&countMaps.has(node.map))counted=true});return !counted}),caseHyps=tuples.map(tuple=>packet(tuple).goal.hyps)
   const frames:FrameCut[]=[],lins:LinCut[]=[],facts=new Map<string,LinCut>(),linearCases=new Set<number>(),composed=new Map<number,{tree:Tree,path:Path}>(),roots=new Map<Tree,Path>()
   const active=inlineFrozenGuard(m.step.flags??{},copy.guard),domain:C={op:'and',xs:[a,b,from,to].flatMap(row=>[{op:'<' as const,a:row,b:bound},{op:'<' as const,a:row,b:n(shape.origin.width)}])}
   const ask=(path:Path,index:number,frame=false,stage='case'):Tree|undefined=>{
    if(late(until))return
    if(frame)for(const [post,map,key]of postReads){const cut={post,pre:read(map.slice(0,-1),key),when:[...path.values()].map(atom=>atom.holds?atom.lin:add(scale(atom.lin,-1),k(1)))};if(options.emitterFramePool){(framePool??=new FrameFactPool(counts,frames,until)).offer(cut)}else if(frameOk(counts,cut))frames.push(cut)}
    const root=framePath(frames,[],path,[],lins),view=mcGoal(stage==='fact'?scalarHyps:caseHyps[index]!,step.decls,request),deadline=Math.min(until,clock()+500),before=fullWork(),remember=(tree:Tree)=>{roots.set(tree,new Map(root));return tree}
    if(!view)return
    const cached=composed.get(index)
    if(cached&&stage==='linear-composed'){
     const end=Math.min(deadline,clock()+25),tree=rebasePath(goal,cached.tree,cached.path,root,end,goal)??replayLinearSkeleton(goal,cached.tree,root,end,{deferCheck:deferred})
     if(tree&&accepts(goal,tree,root)){observe?.({stage,index,reused:true,units:(fullWork()-before)/fullRate});return remember(tree)}
    }
    const direct=solve(rowsAt(view,root),1000)
    if(direct.kind==='refuted'){
     const tree=rebasePath(view,{leaf:direct.steps},root,root,deadline,goal)
     if(tree&&!late(until))return remember(tree)
    }
    const result=growCdcl(view,root,{nodes:0,until:deadline}),tree='tree'in result?rebasePath(view,result.tree,root,root,deadline,goal):undefined
    observe?.({stage,index,checked:!!tree,units:(fullWork()-before)/fullRate,...(!('tree'in result)?{outcome:result.stuck,witness:result.witness}:{})})
    if(!tree||late(until))return
    if(stage==='linear-composed'&&accepts(goal,tree,root))composed.set(index,{tree,path:root})
    return remember(tree)
   }
   const transport=(path:Path,index:number):Tree|undefined=>{
    if(!linearCases.has(index)){
     for(const inst of caseInsts[index]!){
      const dependencies=new Set<string>()
      for(const [,id]of inst.terms){const count=reads.find(read=>read[0]===id)!;if(count[1].endsWith('#'))walkOnce(count[2],(node:any)=>{if(node.op==='var')dependencies.add(node.name)})}
      const when:C[]=[m.pre!,domain,active]
      if(dependencies.has(law.forall!+'#'))when.push(index>=2?same(a,to):not(same(a,to)))
      if(dependencies.has(law.keys![0]!))when.push(index%2?same(b,to):not(same(b,to)))
      const key=json([inst.terms,when]);if(facts.has(key))continue
      const before=fullWork(),fact=guardLinearFact(step.decls,reads,{name:'row copy transport',kind:'ordinary-copy',when,terms:inst.terms},Math.min(until,clock()+100),event=>{if(event.outcome!=='proof')observe?.({stage:'copy-transport-failure',index,witness:event.witness,outcome:event.outcome})})
      observe?.({stage:'copy-transport',index,checked:!!fact,units:(fullWork()-before)/fullRate})
      if(!fact)return
      facts.set(key,fact.cut);lins.push(fact.cut)
     }
     linearCases.add(index)
    }
    return ask(path,index,false,'linear-composed')
   }
   const split=countGuardTree(until),regions=(path:Path)=>split.condition(same(a,to),path,p=>split.condition(same(b,to),p,q=>transport(q,3),q=>transport(q,2)),p=>split.condition(same(b,to),p,q=>transport(q,1),q=>transport(q,0)))
   const copies=(path:Path)=>split.condition(atMost(to,from),path,regions,regions)
   const run=(path:Path)=>split.rows(countFrameConditions(choice),path,p=>split.condition(domain,p,q=>split.condition(active,q,copies,q=>ask(q,0,true)),q=>ask(q,0)),p=>ask(p,0))
   const tree=split.condition(m.pre,new Map(),run,path=>ask(path,0,false,'outside-pre'))
   if(!tree)return decline('tree')
   const stable=stabilizeGuardedTree(goal,tree,frames,lins,roots,until,{deferCheck:deferred})
   if(!stable.tree||late(until))return decline('stabilization')
   if(framePool)observe?.({stage:'emitter-frame-pool',emitter:'copy',...framePool.stats()})
    const cert:CountCert={...request,frames,lins,tree:stable.tree}
   return (options.deferToComposition||checkMC(step.goal.hyps,step.decls,cert))&&!late(until)?{instances,certs:{[step.goal.name]:cert},...(deferred?{status:'unchecked' as const}:{})}:undefined
  }catch(error){if(error===stopped)return;throw error}
 })
}
