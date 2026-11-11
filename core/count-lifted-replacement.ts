import {liftedLeafUntil} from './count-lifted-budget.ts'
import {FrameFactPool} from './count-emitter-frame-pool.ts'
// Generic stored-row replacement proposer. The strict path checks transports;
// composition-only deferral leaves acceptance to the unchanged final checker.
// Discovery supplies roles, never axioms.
import {traceNow} from './trace-clock.ts'
import {proveBooleanPartitionCut} from './count-boolean-partition.ts'
import {type C,type E,type Law,type Machine,all,atMost,get,less,n,not,plus,same,times,walkOnce,x} from './machine.ts'
import {type CountCert,type CountInst,type FrameCut,type Goal,type Instances,type LinCut,type LemmaCut,type Path,type Tree,check,checkMC,countedObligations,frameOk,framePath,lemmaPath,canon,linActive,mcGoal,substC,truth} from '../kernel/kernel.ts'
import {type CountRequestBuilder,type CountStrategyOptions,type CountStrategyProof,deferIntermediateCountChecks} from './count-strategy.ts'
import {discoverLiftedCountGuard,discoverLiftedCountOperation} from './count-lifted-shape.ts'
import {discoverLiftedCountPrerequisites} from './count-lifted-prerequisite.ts'
import {countsForReads} from './count-facts.ts'
import {countFrameConditions,fixedCountFrameCase,ownCountLawInstance} from './count-frames.ts'
import {matchLiftedCountBodies} from './count-lifted-transports.ts'
import {countGuardTree} from './count-guard-tree.ts'
import {inlineFrozenGuard} from './count-frozen-guard.ts'
import {clock,fullRate,fullWork,late,pastWall,rowsAt,usedHyps,withDeadline} from '../kernel/prove.ts'
import {growCdcl} from '../kernel/cdcl.ts'
import {type Lin,add,k,scale,solve} from './solver.ts'
import {rebasePath} from './count-rebase-path.ts'
import {minimalTransportView,minimalViewFirst} from './count-minimal-view.ts'
import {copyQueryContext} from './count-query-context.ts'
import {guardLinearFact} from './count-guard-facts.ts'
import {UnwrittenCountPrefix} from './count-unwritten-prefix.ts'
import {stabilizeGuardedTree} from './count-stabilize-tree.ts'
import {proveQuorumCountLeaf} from './count-quorum-leaf.ts'
const json=(value:unknown)=>JSON.stringify(value)
type Terms=[number,string][]
export function proveLiftedCountReplacement(m:Machine,family:Law[],law:Law,until:number,requestFor:CountRequestBuilder,observe?:(event:Record<string,unknown>)=>void,options:CountStrategyOptions={}):CountStrategyProof|undefined{
 if(!family.includes(law))return
 return withDeadline(until,()=>{
  const deferred=deferIntermediateCountChecks(options),accepts=(goal:Goal,tree:Tree,path?:Path)=>deferred||check(goal,tree,path)
  const c2=options.slicedLemmas===true
  const shape=discoverLiftedCountGuard(m,law,family),choice=fixedCountFrameCase(m),operation=shape&&choice&&discoverLiftedCountOperation(m,shape,choice.value)
  if(!shape||!choice||operation?.kind!=='threshold-replace'||!('write'in operation)||!operation.write||!m.pre||late(until))return
  const write=operation.write,agreement=shape.rowAgreements[0],prerequisites=discoverLiftedCountPrerequisites(m,law,family)
  const stopped={},decline=(reason:string):never=>{observe?.({stage:'replacement-decline',reason,remaining:until-clock(),pastWall:pastWall()});throw stopped}
  let framePool:FrameFactPool|undefined
  try{
   const profileStart=c2?fullWork():0
   if(write.increment!==0||!write.committedInput||!write.committedCount||!agreement||prerequisites.length!==1)return decline('replacement-prerequisites')
   const fields=[shape.countShape.thresholdField,...agreement.shape.fields.filter(field=>field!==shape.countShape.thresholdField)]
   if(fields.length!==2)return decline('version-order')
   const a=x(law.forall!+'#'),b=x(law.keys![0]!),actor=x(write.source),rowMap=shape.origin.rowCount,pair=(p:E,q:E)=>plus(times(shape.origin.width,p),q)
   const twins=new Set(shape.origin.twins.map(twin=>twin.row)),votes=shape.countMaps.filter(map=>map!==rowMap&&!twins.has(map))
   if(votes.length!==1)return decline('disabled-count')
   const vote=votes[0]!,difference=shape.origin.twins[0],reverse=shape.origin.twins[1],intersection=shape.origin.twins[2]
   if(!difference||!reverse||!intersection||difference.row!==reverse.row)return decline('partition-shape')
   const instances:Instances=ownCountLawInstance(law,{[prerequisites[0]!.law.name]:[actor,a,actor,b]})
   const halfInput=(only:string):E=>{
    const names=new Set<string>()
    walkOnce(m.assume,(node:any)=>{
     if(node.op!=='<='||node.a.op!=='mul'||node.a.k!==2||node.a.a.op!=='var'||!m.inputs.includes(node.a.a.name))return
     const maps:string[]=[];let supported=true
     walkOnce(node.b,(part:any)=>{if(part.op==='get'){maps.push(part.map);if(part.key.op!=='const'||part.key.value!==0)supported=false}})
     if(supported&&maps.length===2&&maps.includes(only)&&maps.includes(intersection.request))names.add(node.a.a.name)
    })
    if(names.size!==1)return decline('request-half-input')
    return x([...names][0]!)
   }
   const sourceHalf=halfInput(difference.request),requestHalf=halfInput(reverse.request),[leftHalf,rightHalf]=law.keys!.slice(1).map(x)
   instances[law.name]=[[a,b,leftHalf!,rightHalf!],[actor,a,sourceHalf,leftHalf!],[actor,b,sourceHalf,rightHalf!],[actor,actor,sourceHalf,sourceHalf]].flat()
   const guardFields=new Set(fields),scalarLaws:Law[]=[],markerMaps=new Set(agreement.shape.markers.map(marker=>marker.map)),activeStates=new Set<string>()
   walkOnce(m.step.flags?.[write.guard],(node:any)=>{if(node.op==='var'&&Object.hasOwn(m.state,node.name))activeStates.add(node.name)})
   walkOnce(m.step.flags?.[write.guard],(node:any)=>{if(node.op==='get'&&!m.counts?.[node.map])guardFields.add(node.map)})
   agreement.shape.markers.forEach(marker=>guardFields.add(marker.map))
   for(const candidate of family){
    if(!candidate.forall||(candidate.keys?.length??0)>1)continue
    let valid=true,read=false,versionBound=false;const seenMaps=new Set<string>(),seenStates=new Set<string>()
    walkOnce(candidate.holds,(node:any)=>{if(node.op==='all'||node.op==='flag')valid=false;if(node.op==='var'&&Object.hasOwn(m.state,node.name))seenStates.add(node.name);if(node.op==='get'){read=true;seenMaps.add(node.map);if(!guardFields.has(node.map))valid=false}if(node.op==='<='&&node.a.op==='get'&&node.b.op==='get'&&node.a.map===fields[1]&&node.b.map===fields[1])versionBound=true})
    if(!valid||!read||candidate.keys?.length&&!versionBound||!candidate.keys?.length&&([...seenMaps].some(map=>!markerMaps.has(map))||[...seenStates].some(name=>!activeStates.has(name))))continue
    scalarLaws.push(candidate);instances[candidate.name]=candidate.keys?.length?[actor,a,actor,b]:[a,b,actor]
   }
   const packet=()=>countedObligations(m,family,{[law.name]:instances},family.indexOf(law)).at(-1)!,bootstrap=packet(),reads=[...requestFor(bootstrap.goal,bootstrap.decls).reads]
   let prefix='replacement$';while(json([m,family,reads]).includes(prefix))prefix='$'+prefix
   const bind=(map:string,key:E)=>{const found=reads.find(read=>read[1]===map&&json(read[2])===json(key));if(found)return found[0];const id=prefix+'r'+reads.length;reads.push([id,map,key]);return id}
   const row=countsForReads(bootstrap.decls,[[prefix+'row',rowMap,actor]])?.[0]
   const used=new Set<string>();walkOnce([m.pre,m.assume,m.step.flags?.[write.guard]],(node:any)=>{if(node.op==='get')used.add(node.map)})
   const aliases=Object.entries(m.counts??{}).filter(([map,definition])=>!definition.base&&used.has(map)).flatMap(([map])=>{const count=countsForReads(bootstrap.decls,[[prefix+'alias',map,n(0)]])?.[0];return row&&count&&matchLiftedCountBodies(row,count)?[map]:[]})
   if(aliases.length!==1)return decline('actor-row-alias')
   const X=bind(aliases[0]!,n(0)),Y=bind(write.inputCount,n(0)),Q=bind(write.committedCount,n(0)),dx=bind(difference.request,n(0)),dy=bind(reverse.request,n(0)),mid=bind(intersection.request,n(0)),R=(p:E,post=false)=>bind(rowMap+(post?'#':''),p),V=(p:E,post=false)=>bind(vote+(post?'#':''),p),D=(p:E,q:E,post=false)=>bind(difference.row+(post?'#':''),pair(p,q)),H=(p:E,q:E,post=false)=>bind(intersection.row+(post?'#':''),pair(p,q))
   for(const p of [a,b,actor]){R(p);V(p)}
   for(const [p,q]of [[a,b],[actor,b],[a,actor],[actor,actor]]){D(p!,q!);D(q!,p!);H(p!,q!)}
   for(const p of [a,b]){R(p,true);V(p,true)}D(a,b,true);D(b,a,true);H(a,b,true)
   const counts0=countsForReads(bootstrap.decls,reads),bound=counts0?.find(count=>count.v===Y)?.below
   if(!bound)return decline('count-bound')
   const insts:CountInst[]=[],put=(terms:Terms)=>{const old=insts.findIndex(inst=>json(inst.terms)===json(terms));if(old>=0)return old;insts.push({wit:prefix+'w'+insts.length,below:bound,terms,unit:0});return insts.length-1},both=(terms:Terms)=>[put(terms),put(terms.map(([c,id])=>[-c,id]))]
   const plans=[true,false].map(left=>{
    const written=left?a:b,other=left?b:a,preOverlap=H(actor,other),preActor=D(actor,other),preOther=D(other,actor)
    const equal=[...both([[1,R(other)],[-1,R(actor)]]),...both([[1,D(other,written,true)],[-1,dx]])]
    const older=c2?[put([[1,Q],[1,V(other)],[-1,preActor],[-1,preOther],[-1,preOverlap]]),put([[1,V(other)],[-1,preOther],[-1,preOverlap]]),put([[1,Q],[-1,preActor],[-1,preOverlap]])]:[...both([[1,X],[-1,dx],[-1,mid]]),...both([[1,D(other,written,true)],[1,H(a,b,true)],[-1,preOther],[-1,preOverlap]]),...both([[1,preActor],[1,preOverlap],[-1,X]]),put([[1,R(actor)],[-1,X]]),put([[1,R(other)],[-1,preOther],[-1,preOverlap]]),put([[1,D(other,written,true)],[1,H(a,b,true)],[-1,R(other,true)]]),put([[1,Q],[-1,V(actor)]]),put([[1,Q],[1,V(other)],[-1,preActor],[-1,preOther],[-1,preOverlap]]),put([[1,V(other)],[-1,preOther],[-1,preOverlap]]),put([[1,Q],[-1,preActor],[-1,preOverlap]])]
    const newer=[put([[1,Q],[-1,bind(prerequisites[0]!.voteMap,pair(actor,other))]]),put([[1,R(actor)],[-1,X]])]
    return {left,written,other,equal,older,newer,writtenRow:both([[1,R(written,true)],[-1,Y]])}
   })
   const common=[...both([[1,R(actor)],[-1,X]]),...both([[1,X],[-1,dx],[-1,mid]]),...both([[1,Y],[-1,dy],[-1,mid]])]
   const committedEligible=put([[1,Q],[-1,V(actor)]])
   const witnesses=insts.map(inst=>x(inst.wit))
   instances[agreement.law.name]=plans.flatMap(plan=>plan.equal.flatMap(index=>[actor,plan.other,x(insts[index]!.wit)]))
   const ownFlags=c2?(()=>{
   const ownFlags=new Set<string>(),flagQueue=[write.guard];walkOnce([m.pre,m.assume],(node:any)=>{if(node.op==='flag')flagQueue.push(node.name)});while(flagQueue.length){const name=flagQueue.pop()!;if(ownFlags.has(name))continue;ownFlags.add(name);walkOnce(m.step.flags?.[name],(node:any)=>{if(node.op==='flag')flagQueue.push(node.name)})}
   observe?.({stage:'own-operation-flags',names:[...ownFlags].filter(name=>m.step.flags?.[name]?.op==='all').sort()})
    return ownFlags
   })():undefined
   for(const [name,flag]of Object.entries(m.step.flags??{}))if(flag.op==='all'&&(!ownFlags||ownFlags.has(name)))instances['?'+name]=[a,b,actor,...witnesses]
   const arithmeticHyps=new Map<string,C[]>(),step=packet(),request={reads,insts,picks:[]},goal=mcGoal(step.goal.hyps,step.decls,request),counts=countsForReads(step.decls,reads)
   if(!goal||!counts)return decline('encoding')
   const active=inlineFrozenGuard(m.step.flags??{},write.guard),domain=all(...[a,b,actor].flatMap(p=>[less(p,bound),less(p,n(shape.origin.width))])),frames:FrameCut[]=[],lins:LinCut[]=[],lemmas:LemmaCut[]=[],roots=new Map<Tree,Path>()
   observe?.({stage:'replacement-plan',transports:insts.length,reads:reads.length,scalarPremises:scalarLaws.length,rowAgreement:agreement.law.name,quorumPremise:prerequisites[0]!.law.name})
   const prefixFacts=new UnwrittenCountPrefix(step.decls,reads,[same(x(choice.name),n(choice.value)),m.pre,active],actor,bound,'cdcl',{deferCheck:deferred,leafUnits:options.leafUnits}),done=new Set<string>()
   const fact=(terms:Terms,when:C[],stage:string):boolean=>{
    const key=json([terms,when]);if(done.has(key))return true
    const start=fullWork(),startWall=observe?traceNow():0,result=c2&&stage==='partition'?proveBooleanPartitionCut(counts,when,terms,liftedLeafUntil(until,options,500),observe):guardLinearFact(step.decls,reads,{name:'replacement '+stage,kind:'ordinary-replacement-definition',when,terms},liftedLeafUntil(until,options,100),event=>{if(c2){if(event.outcome!=='proof'&&event.outcome!=='proposal')observe?.({stage:'cut-refused',kind:'linear',label:stage,outcome:event.outcome,witness:event.witness,when,terms,counts:counts.filter(count=>terms.some(([,id])=>id===count.v))})}else{if(event.outcome!=='proof')observe?.({stage:stage+'-failure',outcome:event.outcome,witness:event.witness})}},'cdcl',{deferCheck:deferred})
    observe?.({stage,checked:!deferred&&!!result,proposed:!!result,units:(fullWork()-start)/fullRate,wallMs:traceNow()-startWall});if(!result)return false
    lins.push(result.cut);done.add(key);return true
   }
   const prepare=(post:boolean,region:C[])=>{
    const when:C[]=c2?[]:[same(x(choice.name),n(choice.value)),m.pre!,domain,active,...region]
    for(const p of [a,b])for(const sign of [1,-1])if(!fact([[sign,D(p,json(p)===json(a)?b:a,post)],[sign,H(a,b,post)],[-sign,R(p,post)]],when,'partition'))return false
    return true
   }
   const unwritten=(p:E)=>{
    for(const [post,pre,sign]of [[R(p,true),R(p),1],[R(p,true),R(p),-1],[V(p,true),V(p),1]] as [string,string,1|-1][]){
     const key=json([post,pre,sign]);if(done.has(key))continue
     if(post===V(p,true)&&sign===1){if(!fact([[1,post],[-1,pre]],[same(x(choice.name),n(choice.value)),m.pre!,domain,active,not(same(p,actor))],'unwritten-disabled'))return false;done.add(key);continue}
     const start=fullWork(),startWall=observe?traceNow():0,cut=prefixFacts.prove(post,pre,[p],sign,until);observe?.({stage:'unwritten-prefix',checked:!deferred&&!!cut,proposed:!!cut,units:(fullWork()-start)/fullRate,wallMs:traceNow()-startWall});if(!cut)return false
     lins.push(cut);done.add(key)
    }
    return true
   }
   const remembered=new Map<string,{tree:Tree,root:Path}[]>()
   const ask=(path:Path,stage:string,index?:number):Tree|undefined=>{
    let selectedLemma:LemmaCut|undefined
    if(late(until))return
    const root=framePath(frames,[],path,[],lins),start=fullWork(),startWall=observe?traceNow():0,end=liftedLeafUntil(until,options,500),cacheKey=stage+':'+index+':'+truth(same(a,actor),path)+':'+truth(same(b,actor),path)
    if(c2&&stage==='older-transport'&&index!==undefined){
     const cut=add(...insts[index]!.terms.map(([c,id])=>({[id]:c}))),known=lemmas.find(l=>canon(l.cut)===canon(cut)&&lemmaPath([l],root).size>root.size)
     if(known){const close=(p:Path):Tree|undefined=>{const r=framePath(frames,lemmas,p,[],lins),out=solve(rowsAt(goal,r),500);if(out.kind!=='refuted')return;const leaf:Tree={leaf:out.steps};roots.set(leaf,new Map(r));return leaf};const main=split.rows(known.when,path,close,close);observe?.({stage:'older-lemma-reuse',index,checked:!!main});return main}
    }
    for(const cached of remembered.get(cacheKey)??[]){
     const tree=rebasePath(goal,cached.tree,cached.root,root,liftedLeafUntil(end,options,25),goal)
     if(tree&&accepts(goal,tree,root)){roots.set(tree,new Map(root));observe?.({stage,index,checked:!deferred,proposed:true,reused:true,units:(fullWork()-start)/fullRate,wallMs:traceNow()-startWall});return tree}
    }
    const older=c2&&stage==='older-transport',postIds=c2?new Set(reads.filter(r=>r[1].endsWith('#')).map(r=>r[0])):undefined,isPost=(value:unknown)=>{let out=false;walkOnce(value,(node:any)=>{if(node.op==='get'&&node.map.endsWith('#')||node.op==='var'&&postIds!.has(node.name))out=true});return out},preRoot:Path=c2?new Map([...root].filter(([,a])=>!Object.keys(a.lin).some(k=>postIds!.has(k)||k.includes('#[')))):root,preGoal=c2?{...goal,hyps:goal.hyps.filter(h=>!isPost(h))}:goal
    const hyps=older?step.goal.hyps.filter(h=>!isPost(h)):arithmeticHyps.get(stage)??(stage.startsWith('equal-')?arithmeticHyps.get('equal-region')!:step.goal.hyps)
    const view=index===undefined?{goal:mcGoal(copyQueryContext(hyps,root,counts,insts,[]),step.decls,{reads,insts:[],picks:[]}),path:root}:minimalTransportView(hyps,step.decls,reads,insts,[insts[index]!],older?preRoot:root)
    if(!view?.goal)return
    const result=stage.startsWith('older-composed')?(()=>{
     const candidate=growCdcl(view.goal!,view.path,{nodes:0,until:end})
     if(!('tree'in candidate)){observe?.({stage:'older-query-decline',outcome:candidate.stuck,why:candidate.why,query:view.goal,path:[...view.path],witness:candidate.witness});return {tree:undefined,minimalKind:candidate.stuck,fallback:false,witness:candidate.witness}}
     const tree=rebasePath(view.goal!,candidate.tree,view.path,root,end,goal)
     return {tree:tree&&accepts(goal,tree,root)?tree:undefined,minimalKind:'proof',fallback:false}
    })():minimalViewFirst(older?preGoal:goal,view.goal,older?preRoot:root,end,growCdcl,view.path,{deferCheck:deferred}),tree=older&&result.tree?rebasePath(preGoal,result.tree,preRoot,root,end,goal):result.tree
    observe?.({stage,index,checked:!deferred&&!!tree,proposed:!!tree,units:(fullWork()-start)/fullRate,wallMs:traceNow()-startWall,minimal:result.minimalKind,fullFallback:result.fallback,leafCap:late(end),activeLins:lins.map(cut=>linActive(cut,root)),...(result.witness?{witness:result.witness}:{})})
    if(!tree||late(end))return
    if(c2&&stage==='older-transport'&&index!==undefined){const plan=plans.find(plan=>plan.older.includes(index));if(!plan)return;
      if(tree){
       const cut=add(...insts[index]!.terms.map(([c,id])=>({[id]:c}))),postIds=new Set(reads.filter(read=>read[1].endsWith('#')).map(read=>read[0]))
       const isPosition=(lin:import('./solver.ts').Lin)=>{const keys=Object.keys(lin).filter(key=>key!=='1');return plan.other.op==='var'&&keys.length===2&&keys.includes(plan.other.name)&&keys.includes(write.source)}
       const isPost=(value:unknown)=>{let found=false;walkOnce(value,(node:any)=>{if(node.op==='get'&&node.map.endsWith('#')||node.op==='var'&&postIds.has(node.name))found=true});return found}
       const filtered=[...root.values()].filter(atom=>!isPosition(atom.lin)&&canon(atom.lin)!==canon(cut))
       const rootFor=(atoms:typeof filtered)=>{const p:Path=new Map();let duplicate=0;for(const atom of [{lin:cut,holds:false},...atoms]){const id=canon(atom.lin);p.set(p.has(id)?'@'+duplicate++:id,atom)}return p}
       const noPosition=rootFor(filtered),positionFree=rebasePath(goal,tree,root,noPosition,until,goal),preAtoms=filtered.filter(atom=>!Object.keys(atom.lin).some(key=>postIds.has(key)||key.includes('#['))),preRoot=rootFor(preAtoms),slice=goal.hyps.map((hyp,i)=>!isPost(hyp)?i:-1).filter(i=>i>=0),preGoal={...goal,hyps:slice.map(i=>goal.hyps[i]!)},preTree=rebasePath(goal,tree,root,preRoot,until,preGoal)
       if(preTree){
        const used=[...usedHyps(preGoal,preTree,preRoot)].sort((a,b)=>a-b),smallSlice=used.map(index=>slice[index]!),smallGoal={...preGoal,hyps:used.map(index=>preGoal.hyps[index]!)},nativeAtoms=preAtoms.map(atom=>({lin:atom.holds?atom.lin:add(scale(atom.lin,-1),k(1)),holds:true}))
        let kept=nativeAtoms,atRoot=rootFor(kept),candidate=rebasePath(preGoal,preTree,preRoot,atRoot,until,smallGoal)
        if(candidate&&check(smallGoal,candidate,atRoot)){
         for(let at=0;at<kept.length&&!late(until);){const short=kept.filter((_,i)=>i!==at),nextRoot=rootFor(short),next=rebasePath(smallGoal,candidate,atRoot,nextRoot,until,smallGoal);if(next&&check(smallGoal,next,nextRoot)){kept=short;atRoot=nextRoot;candidate=next}else at++}
         const lemma={cut,when:kept.map(atom=>atom.lin),slice:smallSlice,tree:candidate};const key=json([lemma.cut,lemma.when,lemma.slice]);selectedLemma=lemmas.find(l=>json([l.cut,l.when,l.slice])===key)??lemma;if(selectedLemma===lemma)lemmas.push(lemma)
         observe?.({stage:'older-inclusion-lemma',left:plan.left,index,before:preAtoms.length,after:kept.length,hyps:smallSlice.length,nativeWhen:true,lemma})
        }else observe?.({stage:'older-inclusion-lemma',left:plan.left,index,nativeWhen:false,before:preAtoms.length})
       }
       observe?.({stage:'older-inclusion-audit',left:plan.left,index,positionFree:!!positionFree&&check(goal,positionFree,noPosition),preOnly:!!preTree&&check(preGoal,preTree,preRoot),when:preAtoms.map(atom=>atom.holds?atom.lin:add(scale(atom.lin,-1),k(1))),cut,slice,removedPositions:[...root.values()].filter(atom=>isPosition(atom.lin)),removedPost:filtered.filter(atom=>!preAtoms.includes(atom))})
      }
    }
    if(c2&&stage==='older-transport'){
     if(!selectedLemma)return decline('older-inclusion-lemma')
     const close=(p:Path):Tree|undefined=>{const r=framePath(frames,lemmas,p,[],lins),out=solve(rowsAt(goal,r),500);if(out.kind!=='refuted'){observe?.({stage:'older-lemma-main-open',index,when:selectedLemma!.when,path:[...p],result:out});return}const leaf:Tree={leaf:out.steps};roots.set(leaf,new Map(r));return leaf}
     const main=split.rows(selectedLemma.when,path,close,close);observe?.({stage:'older-lemma-main',index,checked:!!main,lemmas:lemmas.length});return main
    }
    roots.set(tree,new Map(root));const previous=remembered.get(cacheKey)??[];if(previous.length<8)remembered.set(cacheKey,[...previous,{tree,root:new Map(root)}]);return tree
   }
   const quick=(path:Path):Tree|undefined=>{
    const root=framePath(frames,[],path,[],lins),view=mcGoal(copyQueryContext(step.goal.hyps,root,counts,insts,[]),step.decls,{reads,insts:[],picks:[]})
    if(!view)return
    const result=solve(rowsAt(view,root),2000);if(result.kind!=='refuted')return
    const tree=rebasePath(view,{leaf:result.steps},root,root,until,goal)
    if(tree&&accepts(goal,tree,root)){roots.set(tree,new Map(root));return tree}
    return undefined
   }
   const truncations=(condition:C)=>{const out:C[]=[],seen=new Set<string>();walkOnce(condition,(node:any)=>{if(node.op==='sub'){const guard=atMost(node.b,node.a),key=json(guard);if(!seen.has(key)){seen.add(key);out.push(guard)}}});return out}
   const frame=(path:Path)=>{for(const [post,map,key]of reads.filter(read=>read[1].endsWith('#'))){const pre=reads.find(read=>read[1]===map.slice(0,-1)&&json(read[2])===json(key));if(!pre)continue;const cut={post,pre:pre[0],when:[...path.values()].map(atom=>atom.holds?atom.lin:add(scale(atom.lin,-1),k(1)))};if(options.emitterFramePool){(framePool??=new FrameFactPool(counts,frames,until)).offer(cut)}else if(frameOk(counts,cut))frames.push(cut)}return ask(path,'inactive')}
   const split=countGuardTree(until,{yesFirst:true}),chain=(ids:number[],path:Path,stage:string,finish:(path:Path)=>Tree|undefined):Tree|undefined=>{const [index,...rest]=ids;if(index===undefined)return finish(path);const row=add(...insts[index]!.terms.map(([c,id])=>({[id]:c})));return split.rows([row],path,next=>chain(rest,next,stage,finish),branch=>ask(branch,stage,index))}
   const targetTruncations=truncations(step.goal.hyps.at(-1)!),compose=(path:Path,stage:string,guards:C[]=targetTruncations,at=0):Tree|undefined=>at===guards.length?ask(path,stage):split.condition(guards[at]!,path,p=>compose(p,stage,guards,at+1),p=>compose(p,stage,guards,at+1))
   const branch=(path:Path,left:boolean):Tree|undefined=>{
    const plan=plans.find(plan=>plan.left===left)!
    if(c2){
    for(const [p,q]of [[actor,plan.other],[plan.other,actor]]){
     for(const sign of [1,-1])if(!fact([[sign,D(p!,q!)],[sign,H(actor,plan.other)],[-sign,R(p!)]],[],'partition'))return
     if(!fact([[1,V(p!)],[-1,R(p!)]],[],'partition'))return
    }
    }
    const olderStage='older-composed-'+(left?'left':'right'),tuple=[actor,plan.other,sourceHalf,left?rightHalf!:leftHalf!]
    if(!arithmeticHyps.has(olderStage))arithmeticHyps.set(olderStage,countedObligations(m,family,{[law.name]:{[law.name]:tuple}},family.indexOf(law)).at(-1)!.goal.hyps)
    const oldLaw=substC(law.holds,{vars:Object.fromEntries([law.forall!,...law.keys!].map((name,index)=>[name,tuple[index]!])),maps:{},flags:{}})
    const olderBranch=(path:Path):Tree|undefined=>{
     if(oldLaw.op!=='or'||oldLaw.xs[0]?.op!=='not')return
     const guard=oldLaw.xs[0].x,disabled=atMost(times(2,get(vote,plan.other)),get(rowMap,plan.other))
     const quorum=(at:Path):Tree|undefined=>{
      const root=framePath(frames,[],at,[],lins),needed=new Set([X,Q,V(actor),V(plan.other),R(actor),R(plan.other),D(actor,plan.other),D(plan.other,actor),H(actor,plan.other)])
      const minimal=mcGoal([m.pre!,domain,oldLaw],step.decls,{reads:reads.filter(([id])=>needed.has(id)),insts:[],picks:[]})
      if(!minimal)return
      const start=fullWork(),startWall=observe?traceNow():0,tree=proveQuorumCountLeaf(goal,minimal,root,oldLaw,{first:Q,second:V(plan.other)},[sourceHalf,left?rightHalf!:leftHalf!],until,observe,{deferCheck:deferred,leafUnits:options.leafUnits})
      observe?.({stage:olderStage,checked:!deferred&&!!tree,proposed:!!tree,units:(fullWork()-start)/fullRate,wallMs:traceNow()-startWall})
      if(tree)roots.set(tree,new Map(root));return tree
     }
     return split.condition(disabled,path,p=>c2?(quick(p)??ask(p,'older-disabled')):ask(p,'older-disabled'),p=>chain(plan.older,p,'older-transport',q=>split.condition(guard,q,quorum,r=>c2?(quick(r)??ask(r,olderStage)):ask(r,olderStage))))
    }
    if(!unwritten(plan.other)||!prepare(true,[same(plan.written,actor),not(same(plan.other,actor))]))return
    const equal=(equalPath:Path)=>chain(plan.writtenRow,equalPath,'written-row',writtenPath=>{
     const guards=agreement.shape.markers.map(marker=>same(get(marker.map,plan.other),n(marker.value)))
     const halves=[same(leftHalf!,left?requestHalf:sourceHalf),same(rightHalf!,left?sourceHalf:requestHalf)]
     const inputs=(at:number,p:Path):Tree|undefined=>at===activeTruncations.length?split.condition(active,p,q=>compose(q,'equal-composed'),q=>ask(q,'equal-reactivate')):split.condition(activeTruncations[at]!,p,q=>inputs(at+1,q),q=>inputs(at+1,q))
     const specialize=(at:number,p:Path):Tree|undefined=>at===halves.length?inputs(0,p):split.condition(halves[at]!,p,q=>specialize(at+1,q),q=>ask(q,'equal-half-complement'))
     const marked=(at:number,p:Path):Tree|undefined=>at===guards.length?chain(plan.equal,p,'equal-transport',q=>specialize(0,q)):split.condition(guards[at]!,p,q=>marked(at+1,q),q=>ask(q,'equal-marker'))
     return marked(0,writtenPath)
    })
    const firstOther=get(fields[0]!,plan.other),firstActor=get(fields[0]!,actor),secondOther=get(fields[1]!,plan.other),secondActor=get(fields[1]!,actor)
    return split.condition(less(firstOther,firstActor),path,olderBranch,p=>split.condition(same(firstOther,firstActor),p,q=>split.condition(less(secondOther,secondActor),q,olderBranch,r=>split.condition(same(secondOther,secondActor),r,equal,s=>ask(s,'newer-second-field'))),q=>chain(plan.newer,q,'newer-transport',r=>ask(r,'newer-composed'))))
   }
   const neither=(path:Path)=>{
    if(!unwritten(a)||!unwritten(b))return
    for(const [p,q]of [[a,b],[b,a]])for(const [post,pre]of [[D(p!,q!,true),D(p!,q!)],[H(a,b,true),H(a,b)]])for(const sign of [1,-1] as const){const key=json([post,pre,sign]);if(done.has(key))continue;const cut=prefixFacts.prove(post!,pre!,[a,b],sign,until);if(!cut)return;lins.push(cut);done.add(key)}
    return ask(path,'neither-actor')
   }
   const diagonal=(path:Path)=>{
    const when=[same(x(choice.name),n(choice.value)),m.pre!,domain,active,same(a,actor),same(b,actor)],terms:Terms[]=[[[1,D(a,b,true)]],[[1,D(b,a,true)]]]
    for(const term of terms)if(!fact(term,when,'diagonal-definition'))return
    return ask(path,'both-actor')
   }
   const positions=(path:Path)=>quick(path)??split.condition(same(a,actor),path,p=>split.condition(same(b,actor),p,diagonal,q=>branch(q,true)),p=>split.condition(same(b,actor),p,q=>branch(q,false),neither))
   const baseHyps=countedObligations(m,[law],{[law.name]:{}},0).at(-1)!.goal.hyps.slice(0,-1)
   arithmeticHyps.set('equal-half-complement',baseHyps)
   const equalFamily=[law,agreement.law,...scalarLaws.filter(candidate=>!candidate.keys?.length)],equalInstances=Object.fromEntries(Object.entries(instances).filter(([name])=>name!==law.name))
   arithmeticHyps.set('equal-region',countedObligations(m,equalFamily,{[law.name]:equalInstances},0).at(-1)!.goal.hyps)
   const negated=step.goal.hyps.at(-1),postGuard=negated?.op==='not'&&negated.x.op==='or'?negated.x.xs.find(part=>part.op==='not'):undefined
   if(postGuard?.op!=='not')return decline('post-half-domain')
   const regions=(path:Path)=>chain([committedEligible],path,'committed-eligible',p=>split.condition(less(get(aliases[0]!,n(0)),times(2,get(write.committedCount!,n(0)))),p,q=>split.condition(postGuard.x,q,positions,r=>ask(r,'outside-target-half')),q=>ask(q,'commit-majority')))
   const activeTruncations=truncations(active),activate=(path:Path):Tree|undefined=>split.condition(active,path,regions,frame)
   const run=(path:Path)=>split.rows(countFrameConditions(choice),path,p=>split.condition(domain,p,q=>chain(common,q,'input-partition',activate),p=>ask(p,'outside-domain')),p=>ask(p,'outside-operation'))
   const profileTree=c2?fullWork():0
   const tree=split.condition(m.pre,new Map(),run,path=>ask(path,'outside-pre'))
   if(!tree)return decline('tree')
   let nodes=0,leaves=0;
   if(c2){
   const regionCounts:Record<string,number>={},multipliers:Record<string,Record<string,{atom:Lin,yes:number,no:number,occurrences:number,maxMin:number,branchingOccurrences:number}>>={}
   const region=(p:Path):string=>{
    if(truth(m.pre!,p)!==true)return 'outside-pre'
    if(truth(same(x(choice.name),n(choice.value)),p)!==true)return 'outside-operation'
    if(truth(domain,p)!==true)return 'outside-domain'
    if(truth(active,p)!==true)return 'inactive'
    const ai=truth(same(a,actor),p),bi=truth(same(b,actor),p)
    if(ai===false&&bi===false)return 'A'
    if(ai===true&&bi===true)return 'B'
    if(ai===bi||ai===undefined||bi===undefined)return 'before-position'
    const o=ai?b:a,first=fields[0]!,second=fields[1]!,sameFirst=truth(same(get(first,o),get(first,actor)),p)
    if(truth(less(get(first,o),get(first,actor)),p)===true)return 'C2'
    if(truth(less(get(first,actor),get(first,o)),p)===true)return 'C3b'
    if(sameFirst===true){
     if(truth(same(get(second,o),get(second,actor)),p)===true)return 'C1'
     if(truth(less(get(second,o),get(second,actor)),p)===true)return 'C2'
     if(truth(less(get(second,actor),get(second,o)),p)===true)return 'C3a'
    }
    return 'before-version'
   }
   const measure=(part:Tree,p:Path):Record<string,number>=>{nodes++;if('leaf'in part){leaves++;const name=region(p);regionCounts[name]=(regionCounts[name]??0)+1;return {[name]:1}}const key=canon(part.split),yes=new Map(p),no=new Map(p);yes.set(key,{lin:part.split,holds:true});no.set(key,{lin:part.split,holds:false});const y=measure(part.yes,yes),n=measure(part.no,no),all:Record<string,number>={};for(const name of new Set([...Object.keys(y),...Object.keys(n)])){const a=y[name]??0,b=n[name]??0;all[name]=a+b;const table=multipliers[name]??={};const row=table[key]??={atom:part.split,yes:0,no:0,occurrences:0,maxMin:0,branchingOccurrences:0};row.yes+=a;row.no+=b;row.occurrences++;row.maxMin=Math.max(row.maxMin,Math.min(a,b));if(a>1&&b>1)row.branchingOccurrences++}return all};measure(tree,new Map());observe?.({stage:'replacement-regions',regions:regionCounts,nodes,leaves});observe?.({stage:'replacement-multipliers',regions:Object.fromEntries(['C1','C2','inactive'].map(name=>[name,Object.values(multipliers[name]??{}).filter(row=>row.yes>1&&row.no>1).sort((a,b)=>Math.min(b.yes,b.no)-Math.min(a.yes,a.no))]))})
   }else{const measure=(part:Tree):void=>{nodes++;if('leaf'in part)leaves++;else{measure(part.yes);measure(part.no)}};measure(tree)}

   observe?.({stage:'replacement-tree',nodes,leaves,frames:frames.length,lins:lins.length})
   const profileStable=c2?fullWork():0
   const stable=stabilizeGuardedTree(goal,tree,frames,lins,roots,until,{deferCheck:deferred,...(c2?{lemmas}:{})})
   if(c2)observe?.({stage:'replacement-profile',prepareUnits:(profileTree-profileStart)/fullRate,treeUnits:(profileStable-profileTree)/fullRate,stabilizeUnits:(fullWork()-profileStable)/fullRate,reads})
   observe?.({stage:'replacement-stabilize',checked:!deferred&&!!stable.tree,proposed:!!stable.tree,rebased:stable.rebased,failed:stable.failed})
   if(!stable.tree||late(until))return decline('stabilization')
   if(framePool)observe?.({stage:'emitter-frame-pool',emitter:'replacement',...framePool.stats()})
    const cert:CountCert={...request,frames,lins,...(c2?{lemmas}:{}),tree:stable.tree}
   return (options.deferToComposition||checkMC(step.goal.hyps,step.decls,cert))&&!late(until)?{instances,certs:{[step.goal.name]:cert},...(deferred?{status:'unchecked' as const}:{})}:undefined
  }catch(error){if(error===stopped)return;throw error}
 })
}
