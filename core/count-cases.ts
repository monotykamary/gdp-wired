// Untrusted finite-input case search for a fixed counted certificate. A small
// model/core query chooses ordinary instances; every combined tree is checked
// against the unspecialized counted obligation before it is returned.
import {type C,type Law,type Machine,walkOnce,x} from './machine.ts'
import {type CountCert,type CountDecl,type Goal,type Instances,type Path,type Tree,canon,checkMC,mcGoal} from '../kernel/kernel.ts'
import {atPoint,clock,grow,modelInstances,widen,withDeadline} from '../kernel/prove.ts'
import {modelSequence} from '../kernel/model-sequence.ts'
import {REFUTED} from '../kernel/cdcl.ts'

type Packet={goal:Goal,decls:CountDecl[]}
export type CountCaseOptions={localModels?:boolean,saturate?:boolean,queryMs?:number,coreLimit?:number,units?:boolean,corePointOnly?:boolean,trace?:(event:Record<string,unknown>)=>void}
export function proveCountCases(m:Machine,laws:Law[],at:Instances,cert:Pick<CountCert,'reads'|'insts'>,until:number,build:(at:Instances)=>Packet,options:CountCaseOptions={}):{instances:Instances,cert:CountCert}|undefined {
 return withDeadline(until,()=>{
  const values=new Map<string,Set<number>>()
  walkOnce([m.step,m.assume],(o:any)=>{
    if(o.op!=='=')return
    const [a,b]=o.a.op==='var'?[o.a,o.b]:[o.b,o.a]
    if(a.op!=='var'||b.op!=='const'||!m.inputs.includes(a.name))return
    const vs=values.get(a.name)??new Set<number>();vs.add(b.value);values.set(a.name,vs)
  })
  const choice=[...values].filter(([,v])=>v.size>2&&v.size<=16).sort((a,b)=>b[1].size-a[1].size)[0]
  if(!choice||clock()>=until)return undefined
  const [name,vs]=choice,cuts=[...vs].sort((a,b)=>a-b),path:Path=new Map(),conditions:C[]=[]
  const splitAt=(v:number):Record<string,number>=>v?{[name]:1,'1':-v}:{[name]:1}
  let packet=build(at),root=mcGoal(packet.goal.hyps,packet.decls,cert)
  if(!root)return undefined
  let goal:Goal={...root,name:packet.goal.name}
  const rebuild=()=>{packet=build(at);root=mcGoal(packet.goal.hyps,packet.decls,cert);if(root)goal={...root,name:packet.goal.name};return !!root}
  const fields=laws.filter(l=>{let counted=false;walkOnce(l.holds,(o:any)=>{if(o.op==='get'&&m.counts?.[o.map])counted=true});return !counted})
  const seq=modelSequence(),records:({goal:Goal,tree:Tree,path:Path}|undefined)[]=[],branches:{prefix:C[],path:Path,root:Path,tails:number[]}[]=[]
  const initial=at,merged:Instances={...at},previous=atPoint.on;atPoint.on=!options.corePointOnly
  const coreGrow=(g:Goal,end:number)=>{const before=atPoint.on;atPoint.on=true;try{return grow(g,new Map(),{nodes:0,until:end,units:options.units})}finally{atPoint.on=before}}
  try {
    for(const [i,value] of [...cuts,undefined].entries()){
      if(clock()>=until)return undefined
      const split=value===undefined?undefined:splitAt(value),cut:C|undefined=value===undefined?undefined:{op:'<=',a:x(name),b:{op:'const',value}}
      if(split)path.set(canon(split),{lin:split,holds:true})
      const root=new Map(path),tails=options.saturate&&value!==undefined?cuts.filter(v=>v>value):[]
      for(const v of tails){const lin=splitAt(v);path.set(canon(lin),{lin,holds:true})}
      const prefix:C[]=[...conditions,...cut?[cut]:[],...tails.map(v=>({op:'<=' as const,a:x(name),b:{op:'const' as const,value:v}}))]
      branches.push({prefix,path:new Map(path),root,tails})
      if(options.localModels){at=initial;if(!rebuild())return undefined}
      let tree:Tree|undefined,source:Goal|undefined
      for(let round=0;round<6&&clock()<until;round++){
        const part={name:goal.name,hyps:[...prefix,...goal.hyps]},start=clock(),q=seq(part,Math.min(until,clock()+(options.queryMs??200)))
        options.trace?.({value,stage:'query',round,hyps:part.hyps.length,ms:Math.round(clock()-start),outcome:'tree'in q?'tree':q.stuck,core:q.core?.length})
        if(!('tree'in q)&&q.why===REFUTED&&q.core?.length&&q.core.length<=(options.coreLimit??Infinity)){
          const core={name:goal.name,hyps:q.core.map(j=>part.hyps[j]!)},out=coreGrow(core,Math.min(until,clock()+Math.max(600,(until-clock())/(cuts.length+1-i))))
          options.trace?.({value,stage:'core',hyps:core.hyps.length,outcome:'tree'in out?'tree':out.stuck})
          if('tree'in out){tree=out.tree;source=core}
        }
        if(tree||'tree'in q||q.stuck!=='sat'||!q.witness)break
        const next=modelInstances(m,fields,at,part,q.witness,8)
        if(!next)break
        at=next;if(!rebuild())return undefined
      }
      if(!tree){
        const part={name:goal.name,hyps:[...prefix,...goal.hyps]},out=grow(part,new Map(),{nodes:0,until:Math.min(until,clock()+Math.max(600,(until-clock())/(cuts.length+1-i))),units:options.units})
        options.trace?.({value,stage:'grow',outcome:'tree'in out?'tree':out.stuck})
        if('tree'in out){tree=out.tree;source=part}
      }
      records.push(tree&&source?{goal:source,tree,path:new Map(path)}:undefined)
      if(options.localModels)for(const [n,terms] of Object.entries(at))merged[n]=[...merged[n]??[],...terms.slice(initial[n]?.length??0)]
      for(const v of tails)path.delete(canon(splitAt(v)))
      if(split){path.set(canon(split),{lin:split,holds:false});conditions.push({op:'not',x:cut!})}
    }
    if(options.localModels){at=merged;if(!rebuild())return undefined}
    const missing=records.flatMap((r,i)=>r?[]:[i])
    for(const [j,i] of missing.entries()){
      if(clock()>=until)break
      const {prefix,path:p}=branches[i]!,part={name:goal.name,hyps:[...prefix,...goal.hyps]}
      const out=grow(part,new Map(),{nodes:0,until:Math.min(until,clock()+(until-clock())/(missing.length-j)),units:options.units})
      if('tree'in out)records[i]={goal:part,tree:out.tree,path:p}
    }
    if(records.some(r=>!r))return undefined
    const trees=records.map((r,i)=>{
      let tree=r&&widen(r.goal,goal,r.tree,{},new Map(),r.path)
      if(!tree)return undefined
      const {root,tails}=branches[i]!
      for(let j=tails.length-1;j>=0;j--){
        const before=new Map(root)
        for(const v of tails.slice(0,j)){const lin=splitAt(v);before.set(canon(lin),{lin,holds:true})}
        const upper=[...before.keys()].indexOf(canon(splitAt(cuts[i]!))),bad=before.size
        if(upper<0)return undefined
        tree={split:splitAt(tails[j]!),yes:tree,no:{leaf:[{kind:'input',index:upper},{kind:'input',index:bad},{kind:'combine',a:0,b:1,ma:1,mb:1}]}}
      }
      return tree
    })
    let tree=trees.at(-1)
    for(let i=cuts.length-1;i>=0;i--)tree=tree&&trees[i]?{split:splitAt(cuts[i]!),yes:trees[i]!,no:tree}:undefined
    const result=tree&&{...cert,tree}
    return result&&checkMC(packet.goal.hyps,packet.decls,result)?{instances:at,cert:result}:undefined
  } finally {atPoint.on=previous}
 })
}
