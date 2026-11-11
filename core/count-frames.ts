// Untrusted, opt-in frame-first search for an explicitly fixed finite operation.
// No protocol names or values are built in. The returned certificate is checked
// against the original obligation; no inferred frame is accepted as an axiom.
import {type C,type E,type Law,type Machine,n,same,x} from './machine.ts'
import {type CountCert,type CountDecl,type FrameCut,type MonoCut,type Goal,type Instances,type Path,type Tree,canon,checkMC,frameOk,framePath,mcGoal,monoOk} from '../kernel/kernel.ts'
import {clock,fullRate,fullWork,grow,pastWall} from '../kernel/prove.ts'
import {growCdcl} from '../kernel/cdcl.ts'
import {countsForReads} from './count-facts.ts'
import {finiteCountChoice} from './count-cases.ts'
import {countSearchView, proveCountQuery} from './count-query.ts'
import type {Lin} from './solver.ts'

export type FixedCountFrameCase={name:string,value:number,values:number[]}
export function fixedCountFrameCase(m:Machine):FixedCountFrameCase|undefined{
 const choice=finiteCountChoice(m)
 if(!choice)return
 const [name,values]=choice,fixed=new Set<number>()
 const visit=(c:C):void=>{
  if(c.op==='and'){c.xs.forEach(visit);return}
  if(c.op!=='=')return
  const [a,b]=c.a.op==='var'?[c.a,c.b]:[c.b,c.a]
  if(a.op==='var'&&a.name===name&&b.op==='const')fixed.add(b.value)
 }
 if(m.assume)visit(m.assume)
 if(fixed.size!==1)return
 const value=[...fixed][0]!
 if(!Number.isSafeInteger(value)||value<0||!values.has(value))return
 return {name,value,values:[...values].sort((a,b)=>a-b)}
}
export function ownCountLawInstance(law:Law,at:Instances):Instances{
 if(!law.forall)return at
 const tuple:E[]=[x(`${law.forall}#`),...(law.keys??[]).map(x)],had=at[law.name]??[],key=JSON.stringify(tuple)
 for(let i=0;i<had.length;i+=tuple.length)if(JSON.stringify(had.slice(i,i+tuple.length))===key)return at
 return {...at,[law.name]:[...had,...tuple]}
}
export function countFrameConditions(choice:FixedCountFrameCase):Lin[]{
 const {name,value,values}=choice
 const rows:Lin[]=[{[name]:1,'1':-value},{[name]:-1,'1':value},...values.filter(v=>v!==value).map(v=>v<value?{[name]:-1,'1':v+1}:{[name]:1,'1':1-v})]
 const normalized=rows.map(row=>Object.fromEntries(Object.entries(row).filter(([,coefficient])=>coefficient!==0)))
 return [...new Map(normalized.map(row=>[canon(row),row])).values()]
}
export type CountCutTrace={kind:'frame'|'mono',post:string,pre:string,checked:boolean,why?:string}
export function proveCountFrameGoal(raw:Goal,decls:CountDecl[],request:Pick<CountCert,'reads'|'insts'|'picks'|'lemmas'>,choice:FixedCountFrameCase,targets:ReadonlySet<string>,until:number,trace?:(cut:CountCutTrace)=>void,options:{deferCheck?:boolean,minimalView?:boolean,leafUnits?:number,trace?:(event:Record<string,unknown>)=>void,extraWhen?:Lin[]}={}):CountCert|undefined{
 if(clock()>=until||pastWall())return
 const goal=mcGoal(raw.hyps,decls,request),counts=countsForReads(decls,request.reads)
 if(!goal||!counts)return
 const when=[...countFrameConditions(choice),...(options.extraWhen??[])],frames:FrameCut[]=[],monos:MonoCut[]=[]
 const conditions:C[]=[same(x(choice.name),n(choice.value))]
 for(const [post,map,key]of request.reads){
  if(!map.endsWith('#')||!targets.has(map.slice(0,-1)))continue
  const pre=request.reads.find(r=>r[1]===map.slice(0,-1)&&JSON.stringify(r[2])===JSON.stringify(key))
  if(!pre)continue
  const f={when,post,pre:pre[0]}
  const equal=frameOk(counts,f)
  trace?.({kind:'frame',post,pre:pre[0],checked:equal})
  if(equal){frames.push(f);continue}
  const postCount=counts.find(c=>c.v===post)!,preCount=counts.find(c=>c.v===pre[0])!
  if(postCount.key!==preCount.key||clock()>=until||pastWall())continue
  const auxiliary:Goal={name:'per-key cut',hyps:[...conditions,{op:'<',a:x(postCount.key),b:postCount.below},{op:'<',a:preCount.body,b:postCount.body}]}
  const out=grow(auxiliary,new Map(),{nodes:0,until:Math.min(until,clock()+100)})
  const cut='tree'in out?{when:conditions,post,pre:pre[0],tree:out.tree}:undefined
  const checked=!!cut&&monoOk(counts,cut)
  trace?.({kind:'mono',post,pre:pre[0],checked,...('stuck'in out?{why:out.stuck}:{})})
  if(cut&&checked)monos.push(cut)
 }
 if(!frames.length&&!monos.length)return
 const minimal=options.minimalView?countSearchView(raw,decls,request):undefined
 const ask=(path:Path):Tree|undefined=>{
  if(clock()>=until||pastWall())return
  if(minimal)return proveCountQuery(goal,framePath(frames,request.lemmas??[],path,monos),until,{query:'frame-leaf',minimal,leafUnits:options.leafUnits,trace:options.trace,deferCheck:options.deferCheck})
  const start=fullWork(),at=framePath(frames,request.lemmas??[],path,monos)
  const out=growCdcl(goal,at,{nodes:0,until:Math.min(until,clock()+(options.leafUnits??Infinity))})
  options.trace?.({query:'frame-leaf',outcome:'tree'in out?'proposed':out.stuck,units:(fullWork()-start)/fullRate,remaining:until-clock(),hyps:goal.hyps.length,path:[...at.values()],...(!('tree'in out)?{goal}: {})})
  return 'tree'in out?out.tree:undefined
 }
 const search=(i:number,path:Path):Tree|undefined=>{
  if(clock()>=until||pastWall())return
  if(i===when.length)return ask(path)
  const row=when[i]!,known=path.get(canon(row))?.holds
  if(known===true)return search(i+1,path)
  if(known===false)return ask(path)
  const yes=search(i+1,new Map(path).set(canon(row),{lin:row,holds:true}))
  if(!yes)return
  const no=ask(new Map(path).set(canon(row),{lin:row,holds:false}))
  return no?{split:row,yes,no}:undefined
 }
 const tree=search(0,new Map())
 if(!tree)return
 const cert={...request,tree,frames,monos}
 return options.deferCheck||checkMC(raw.hyps,decls,cert)?cert:undefined
}
