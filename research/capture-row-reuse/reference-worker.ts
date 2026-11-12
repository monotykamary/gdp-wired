// Separate-process differential control: identical cold/warm memo history in
// each arm. This is a synthetic functional test, not an MLDR admission.
import {createHash} from 'node:crypto'
import {type C,atMost,get,less,min,n,tuple,x} from '../../core/machine.ts'
import {type CountCert,type Count,type Goal,type Path,type Tree,canon,checkGoalLemmas,framePath,leafConstraints,linear} from '../../kernel/kernel.ts'
import {leafRowsOf,rowsAt} from '../../kernel/prove.ts'
import {countedScopeHyps} from '../../core/count-scope-hyps.ts'
import {referenceCountedScopeHyps} from './reference-count-scope-hyps.ts'
import {BudgetExpired,workLedger,withWorkAdmissionTrace} from '../../core/work-admission.ts'
import {workAmount} from '../../core/work-amount.ts'
const mode=process.argv[2]
if(mode!=='reference'&&mode!=='reuse')throw Error('expected reference or reuse')
const collect=mode==='reference'?referenceCountedScopeHyps:countedScopeHyps
function fixture(kind:string,id:string){
 const v=(name:string)=>x(id+name)
 const key=kind==='tuple'?tuple([v('i'),v('a')]):v('i'),other=kind==='tuple'?tuple([v('j'),v('a')]):v('j')
 const a=get('M'+id,key),b=get('M'+id,other)
 const hyps:C[]=[less(a,n(0)),atMost(b,n(99))]
 if(kind==='duplicate')hyps.push(atMost(b,n(100)))
 if(kind==='term')hyps.push(atMost(min(min(a,v('y')),v('z')),n(100)))
 if(kind==='dense')for(let i=0;i<12;i++)hyps.push(atMost(get('M'+id,v('i'+i)),n(100)))
 const goal:Goal={name:'capture '+id,hyps},counts:Count[]=[{v:id+'post',key:id+'k',below:n(0),body:n(0)},{v:id+'pre',key:id+'k',below:n(0),body:n(0)}]
 const cert:CountCert={reads:[],insts:[],tree:{leaf:[]}}
 if(kind==='cuts'){
  cert.frames=[{when:[],post:id+'post',pre:id+'pre'}]
  const aux:Goal={name:'aux',hyps:[less(x(id+'k'),n(0)),less(n(0),n(0))]},rs=leafConstraints(aux,new Map())
  const at=rs.findIndex(r=>r.src&&'fact'in r.src&&r.src.fact===0)
  // A zero bound makes the first per-key hypothesis a constant contradiction
  // only if its naturality is also used. Use the explicit body contradiction.
  void at
  const impossible=rs.findIndex(r=>(r.lin['1']??0)>0&&Object.keys(r.lin).every(k=>k==='1'))
  const tree:Tree={leaf:[{kind:'input',index:impossible}]}
  cert.monos=[{when:[],post:id+'post',pre:id+'pre',tree}]
  cert.lins=[{when:[],pos:[[1,id+'post']],neg:[[1,id+'pre']],tree}]
  cert.lemmas=[{when:[],cut:{},slice:[],tree:{leaf:[{kind:'input',index:0}]}}]
 }
 const mi=Object.keys(linear(a,new Map())!)[0]!,mj=Object.keys(linear(b,new Map())!)[0]!
 const make=(path:Path,pair:boolean):Tree=>{
  const rows=leafConstraints(goal,framePath(cert.frames??[],cert.lemmas??[],path,cert.monos??[],cert.lins??[]))
  const fact=rows.findIndex(r=>r.src&&'fact'in r.src&&r.src.fact===0),nat=rows.findIndex(r=>r.src&&'nat'in r.src&&r.src.nat===(pair?mj:mi))
  const eq=pair?rows.findIndex(r=>r.src&&'pair'in r.src&&r.lin[mj]===1&&r.lin[mi]===-1):-1
  if(fact<0||nat<0||pair&&eq<0)throw Error('fixture row absent')
  let tree:Tree=pair?{leaf:[{kind:'input',index:fact},{kind:'input',index:eq},{kind:'combine',a:0,b:1,ma:1,mb:1},{kind:'input',index:nat},{kind:'combine',a:2,b:3,ma:1,mb:1}]}:{leaf:[{kind:'input',index:fact},{kind:'input',index:nat},{kind:'combine',a:0,b:1,ma:1,mb:1}]}
  if(kind==='products'&&pair)tree={...tree,squares:[{[mi]:1}],products:[[eq,eq],[rows.length+1,rows.length+1]]}
  if(kind==='empty-arrays')tree={...tree,squares:[],products:[]}
  if(kind==='sparse'||kind==='empty-arrays')leafRowsOf.set(tree,{n:rows.length,at:new Map(rows.map((r,i)=>[i,{lin:r.lin,src:r.src&&'fact'in r.src?r.src.fact:-1}] as const))})
  return tree
 }
 if(['pair','tuple','products','duplicate','eviction'].includes(kind)){
  const yesLin={[id+'i']:1,[id+'j']:-1},noLin={[id+'j']:1,[id+'i']:-1}
  const branch=(p:Path,l:Record<string,number>,holds:boolean)=>new Map(p).set(canon(l),{lin:l,holds})
  const yes=branch(new Map(),yesLin,true)
  cert.tree={split:yesLin,yes:{split:noLin,yes:make(branch(yes,noLin,true),true),no:make(branch(yes,noLin,false),false)},no:make(branch(new Map(),yesLin,false),false)}
 }else cert.tree=make(new Map(),false)
 return {goal,cert,counts}
}
const outputs:unknown[]=[]
function run(kind:string,id:string,grant:bigint,repeat=1){
 const f=fixture(kind,id)
 // Force the legacy pass to evict an earlier leaf's entry mid-walk. A cache
 // miss must keep the old native build, never trigger a new proposer build.
 if(kind==='eviction')for(let i=0;i<4095;i++){const lin={['primer'+i]:1};rowsAt(f.goal,new Map([[canon(lin),{lin,holds:true}]]))}
 const valid=checkGoalLemmas(f.goal,f.cert.tree,f.cert.lemmas??[],f.cert.frames??[],f.counts,f.cert.monos??[],f.cert.lins??[])
 if(!valid)throw Error('invalid native fixture '+kind)
 const before=JSON.stringify(f.cert),digest=createHash('sha256');let starts=0,error:unknown,refs:number[][]=[]
 workLedger.withBudget(workAmount(grant),()=>withWorkAdmissionTrace(event=>{
  // Bind complete per-operation counters, sites, reservation/lease order and
  // refusal state, not just the final scalar work total.
  digest.update(JSON.stringify(event));starts++
 },()=>{
  try{for(let i=0;i<repeat;i++)refs.push([...(collect(f.goal,f.cert)??[])])}
  catch(e){error=e}
 }))
 if(JSON.stringify(f.cert)!==before)throw Error('certificate changed')
 let rowsEqual=true
 if(!error){
  const verify=(tree:Tree,path:Path):void=>{
   if('leaf'in tree){const actual=framePath(f.cert.frames??[],f.cert.lemmas??[],path,f.cert.monos??[],f.cert.lins??[]);rowsEqual&&=JSON.stringify(rowsAt(f.goal,actual))===JSON.stringify(leafConstraints(f.goal,actual));return}
   const id=canon(tree.split);verify(tree.yes,new Map(path).set(id,{lin:tree.split,holds:true}));verify(tree.no,new Map(path).set(id,{lin:tree.split,holds:false}))
  }
  verify(f.cert.tree,new Map())
  if(!rowsEqual)throw Error('proposer/native row bytes differ')
 }
 outputs.push({kind,id,grant:String(grant),valid,rowsEqual,refs,certificate:before,events:starts,trace:digest.digest('hex'),counters:workLedger.snapshot().counters,error:error instanceof Error?{name:error.name,message:error.message,phase:error instanceof BudgetExpired?error.phase:null,capacity:workLedger.capacityRefusal(error)??null}:error??null})
}
for(const kind of ['plain','pair','tuple','products','duplicate','term','dense','cuts','sparse','eviction','empty-arrays'])run(kind,kind+'_',100000000n,2)
for(const grant of [0n,2n,17n,101n,701n,3001n,10001n])run('pair','limited_'+grant+'_',grant)
console.log(JSON.stringify(outputs))
