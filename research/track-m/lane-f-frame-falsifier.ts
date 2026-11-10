// A concrete interpreted source-frame counterexample, not a CTI claim.
import {readFileSync} from 'node:fs'
import {unpack} from './section18-codec.ts'
import {certFor} from '../../core/counts.ts'
import {focusCountCert} from '../../core/count-focused.ts'
import {finiteEvaluator} from '../../core/finite-houdini.ts'
import {type C,carriedView,evalC,evalE,interpret,walkOnce} from '../../core/machine.ts'
import {canon,mcGoal,termColumn,type Path} from '../../kernel/kernel.ts'
import {piecesAt,walkLive} from '../../core/count-recovery/live-dependencies.ts'
const {p}=unpack(readFileSync('context.json','utf8')),family=JSON.parse(readFileSync('family.json','utf8')),m=p.m
for(const [i,t]of p.columns.entries())if(termColumn(t)!==`⟦${i}⟧`)throw Error('column restore')
const params={size:2},request={op:0,i:0,j:0,hx:0,hy:0,S:new Map([[0,1]]),Q2:new Map<number,number>()},runner=interpret(m),pre=runner.init(params),post=runner.step(params,pre,request),judge=finiteEvaluator(m)
const pres=family.laws.map((l:any)=>({law:l.name,value:judge(l,params,pre)})),posts=family.laws.map((l:any)=>({law:l.name,value:judge(l,params,post)}))
const before=carriedView(m,pre,request,undefined,params),after=carriedView(m,post,request,undefined,params),env:Record<string,number>={...params,...Object.fromEntries(Object.entries(request).filter(([,v])=>typeof v==='number')),'a$quorum#':0,'b$quorum':1}
for(const [name,q]of Object.entries(m.step.flags??{}))env['?'+name]=Number(evalC(q as any,env,before,m))
const cert=focusCountCert(m,p.packet.decls,certFor(p.packet.goal,p.packet.decls,true,1000),{structural:false,frames:true,algebraic:true,requestFrames:true,copyFrames:true,claim:p.packet.goal.hyps.at(-1)}),values=new Map<string,number>()
walkOnce(cert.reads,(o:any)=>{if(o.op==='var'&&!(o.name in env))env[o.name]=0})
for(const [id,map,key]of cert.reads)values.set(id,evalE({op:'get',map:map.replace(/#$/,''),key},env,map.endsWith('#')?after:before,m))
const inst=cert.insts.find(q=>JSON.stringify(q.terms)===JSON.stringify([[1,'r$0'],[-1,'r$10']]))!,sum=inst.terms.reduce((n:number,[k,id]:[number,string])=>n+k*values.get(id)!,0),bound=inst.unit*evalE(inst.below,env,before,m),g=mcGoal(p.packet.goal.hyps,p.packet.decls,cert)!,path:Path=new Map(JSON.parse(readFileSync('offdiag-trace.json','utf8')).events.filter((e:any)=>e.stage==='closure-final').at(-1).path),raw=g.hyps.slice(0,-cert.insts.length),ids=new Set(cert.reads.map((r:any)=>r[0])),maps=new Set(cert.reads.map((r:any)=>r[1])),wits=new Set(cert.insts.map((q:any)=>q.wit))
// Check the opposite ordering of the same off-diagonal row case.
for(const lin of [{'b$quorum':1,i:-1},{'b$quorum':-1,i:1}])path.set(canon(lin),{lin,holds:Object.entries(lin).reduce((n,[k,v])=>n+v*env[k]!,0)<=0})
const source=raw.flatMap((c:any)=>piecesAt(c,path)).filter((c:any)=>{let skip=false;const owners=new Set<string>();walkLive(c,path,(o:any)=>{if(o.op==='get'&&maps.has(o.map)||o.op==='var'&&ids.has(o.name))skip=true;else if(o.op==='var'&&wits.has(o.name))owners.add(o.name)});return !skip&&owners.size<=1&&(!owners.size||owners.has(inst.wit))})
walkOnce(source,(o:any)=>{if(o.op==='var'&&!(o.name in env))env[o.name]=0})
const view={...before,maps:{...before.maps,...Object.fromEntries(Object.entries(after.maps).map(([k,v])=>[k+'#',v]))}}
const failed=source.flatMap<{index:number,condition:C}|{index:number,error:string}>((c:any,index:number)=>{try{return evalC(c,env,view,m)?[]:[{index,condition:c}]}catch(e){return [{index,error:String(e)}]}}),pathValues=[...path].map(([key,{lin,holds}])=>({key,holds,value:Object.entries(lin).reduce((n,[k,v])=>n+v*(k==='1'?1:env[k]??NaN),0)}))
if(!pres.every((x:any)=>x.value===true)||failed.length||sum<=bound||pathValues.some(x=>!Number.isFinite(x.value)||(x.value<=0)!==x.holds))throw Error('frame counterexample not established')
console.log(JSON.stringify({familySize:family.laws.length,preFamily:pres.every((x:any)=>x.value===true),preFailures:pres.filter((x:any)=>x.value!==true),postTarget:posts[family.targets.overlap],enabled:true,request:{...request,S:[...request.S],Q2:[]},inst,values:inst.terms.map(([k,id]:[number,string])=>({k,id,value:values.get(id),read:cert.reads.find((r:any)=>r[0]===id)})),sum,bound,frameHolds:sum<=bound,sourceHyps:source.length,failed,pathValues}))
