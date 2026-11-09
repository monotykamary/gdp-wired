// Research-only, opt-in wall accounting. Wrappers delegate unchanged arguments
// to the original functions; exclusive buckets subtract nested measured work.
import {type Tree,check as kernelCheck,checkMC as kernelCheckMC,countedObligations as obligations,mcGoal as makeGoal} from '../../kernel/kernel.ts'
import {grow as kernelGrow,widen as kernelWiden,rowsAt as kernelRowsAt} from '../../kernel/prove.ts'
import {modelSequence as sequence} from '../../kernel/model-sequence.ts'
import {cdclStats} from '../../kernel/cdcl.ts'
import {solve as solveRows,refuteFast as fastRows} from '../../core/solver.ts'
import {certFor as proposeCert} from '../../core/counts.ts'
import {treeMetrics} from './tree-diagnosis.ts'

type Bucket={calls:number,wallMs:number,inclusiveMs:number,trees:number,nodes:number,leaves:number,maxNodes:number,maxLeaves:number,maxDepth:number}
export class WallProfiler{
 readonly buckets=new Map<string,Bucket>()
 private stack:{child:number}[]=[]
 constructor(public enabled=false,private now=()=>performance.now()){}
 private bucket(name:string):Bucket{let b=this.buckets.get(name);if(!b){b={calls:0,wallMs:0,inclusiveMs:0,trees:0,nodes:0,leaves:0,maxNodes:0,maxLeaves:0,maxDepth:0};this.buckets.set(name,b)}return b}
 run<T>(name:string,f:()=>T):T{
  if(!this.enabled)return f()
  const start=this.now(),frame={child:0};this.stack.push(frame)
  try{return f()}finally{
   const elapsed=this.now()-start;this.stack.pop()
   const b=this.bucket(name);b.calls++;b.inclusiveMs+=elapsed;b.wallMs+=elapsed-frame.child
   const parent=this.stack.at(-1);if(parent)parent.child+=elapsed
  }
 }
 // An already measured native subphase (CDCL's own unfold timer).
 native(name:string,ms:number):void{
  if(!this.enabled||ms<=0)return
  const b=this.bucket(name);b.calls++;b.wallMs+=ms;b.inclusiveMs+=ms
  const parent=this.stack.at(-1);if(parent)parent.child+=ms
 }
 sample(name:string,tree:Tree|undefined):void{
  if(!this.enabled||!tree)return
  this.run('instrumentation',()=>{const m=treeMetrics(tree),b=this.bucket(name);b.trees++;b.nodes+=m.nodes;b.leaves+=m.leaves;b.maxNodes=Math.max(b.maxNodes,m.nodes);b.maxLeaves=Math.max(b.maxLeaves,m.leaves);b.maxDepth=Math.max(b.maxDepth,m.depth)})
 }
 snapshot(){return Object.fromEntries([...this.buckets].map(([name,b])=>[name,{...b,wallMs:Math.round(b.wallMs*1000)/1000,inclusiveMs:Math.round(b.inclusiveMs*1000)/1000}]))}
}
export const wallProfile=new WallProfiler(process.env.LAB_WALL_PROFILE==='1')
if(wallProfile.enabled)cdclStats.on=true
const boot=(globalThis as {trackMWallStart?:number}).trackMWallStart??performance.now(),stages:{name:string,wallMs:number}[]=[]
export const wallStage=(name:string):void=>{if(wallProfile.enabled)stages.push({name,wallMs:Math.round((performance.now()-boot)*1000)/1000})}
export const wallSpan=<T>(name:string,f:()=>T):T=>wallProfile.run(name,f)
function measured<T>(name:string,f:()=>T,tree?:(value:T)=>Tree|undefined):T{const out=wallSpan(name,f);if(tree)wallProfile.sample(name,tree(out));return out}
export const wallTree=<T extends Tree|undefined>(name:string,f:()=>T):T=>measured(name,f,tree=>tree)
const checkSites=new Map<string,{calls:number,wallMs:number,nodes:number,leaves:number}>()
export const check:typeof kernelCheck=(...args)=>{
 if(!wallProfile.enabled||process.env.LAB_WALL_CHECK_SITES!=='1')return measured('source-check',()=>kernelCheck(...args),()=>args[1])
 const site=new Error().stack?.split('\n').find(line=>line.includes('/research/track-m/')&&!line.includes('/wall-profile.ts'))?.trim()??'unknown',started=performance.now()
 try{return measured('source-check',()=>kernelCheck(...args),()=>args[1])}finally{
  const elapsed=performance.now()-started,m=treeMetrics(args[1]),old=checkSites.get(site)??{calls:0,wallMs:0,nodes:0,leaves:0}
  old.calls++;old.wallMs+=elapsed;old.nodes+=m.nodes;old.leaves+=m.leaves;checkSites.set(site,old)
 }
}
export const finalCheck:typeof kernelCheck=(...args)=>measured('final-source-check',()=>kernelCheck(...args),()=>args[1])
export const checkMC:typeof kernelCheckMC=(...args)=>measured('final-checkMC',()=>kernelCheckMC(...args),()=>args[2].tree)
export const widen:typeof kernelWiden=(...args)=>measured('transport',()=>kernelWiden(...args),tree=>tree)
export const rowsAt:typeof kernelRowsAt=(...args)=>wallSpan('row-construction',()=>kernelRowsAt(...args))
export const solve:typeof solveRows=(...args)=>wallSpan('arithmetic-search',()=>solveRows(...args))
export const refuteFast:typeof fastRows=(...args)=>wallSpan('arithmetic-search',()=>fastRows(...args))
export const countedObligations:typeof obligations=(...args)=>wallSpan('goal-build',()=>obligations(...args))
export const mcGoal:typeof makeGoal=(...args)=>wallSpan('goal-build',()=>makeGoal(...args))
export const certFor:typeof proposeCert=(...args)=>wallSpan('instance-generation',()=>proposeCert(...args))
export const grow:typeof kernelGrow=(...args)=>measured('cdcl-search',()=>{
 const before=cdclStats.unfoldMs
 try{return kernelGrow(...args)}finally{wallProfile.native('tree-unfold',cdclStats.unfoldMs-before)}
},out=>'tree'in out?out.tree:undefined)
export const modelSequence:typeof sequence=(...args)=>{
 const query=sequence(...args)
 return (...params)=>measured('cdcl-search',()=>query(...params),out=>'tree'in out?out.tree:undefined)
}
export function wallReport():object{
 const elapsed=performance.now()-boot,buckets=wallProfile.snapshot(),accounted=[...wallProfile.buckets.values()].reduce((n,b)=>n+b.wallMs,0)
 return {enabled:wallProfile.enabled,...(checkSites.size?{checkSites:Object.fromEntries(checkSites)}:{}),totalWallMs:Math.round(elapsed*1000)/1000,accountedWallMs:Math.round(accounted*1000)/1000,unattributedWallMs:Math.round((elapsed-accounted)*1000)/1000,stages,buckets,nativeCdcl:{runs:cdclStats.runs,decisions:cdclStats.decisions,setupMs:cdclStats.setupMs,unfoldMs:cdclStats.unfoldMs,leaves:cdclStats.leaves,resolved:cdclStats.resolved}}
}
