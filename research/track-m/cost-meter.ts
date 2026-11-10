// Measurement only. No proof data, deadline, cost counter or outcome is changed.
export type CostPhase='generation'|'search'|'construction'|'kernel'
type Frame={phase:CostPhase,lock:boolean,children:number,start:number}
type Stat={calls:number,exclusiveMs:number,inclusiveMs:number}
export class CostMeter{
 readonly phases=new Map<CostPhase,Stat>()
 readonly sites=new Map<string,Stat>()
 private stack:Frame[]=[]
 constructor(public enabled=false,private now=()=>performance.now()){}
 run<T>(phase:CostPhase,site:string,f:()=>T,lock=false):T{
  if(!this.enabled)return f()
  const parent=this.stack.at(-1)
  if(parent?.phase==='kernel'||phase==='kernel'){phase='kernel';lock=true}
  else if(parent?.lock){phase=parent.phase;lock=true}
  const frame={phase,lock,children:0,start:this.now()};this.stack.push(frame)
  try{return f()}finally{
   const elapsed=this.now()-frame.start;this.stack.pop()
   const exclusive=elapsed-frame.children
   for(const [map,key] of [[this.phases,phase],[this.sites,site]] as const){
    const s=map.get(key as never)??{calls:0,exclusiveMs:0,inclusiveMs:0}
    s.calls++;s.exclusiveMs+=exclusive;s.inclusiveMs+=elapsed;map.set(key as never,s)
   }
   if(parent)parent.children+=elapsed
  }
 }
 snapshot(){
  const project=(stats:Map<string,Stat>)=>Object.fromEntries([...stats].map(([k,v])=>[k,{...v,exclusiveMs:Math.round(v.exclusiveMs*1000)/1000,inclusiveMs:Math.round(v.inclusiveMs*1000)/1000}]))
  return {phases:project(this.phases),sites:project(this.sites)}
 }
}
export const costMeter=new CostMeter(process.env.TRACK_M_COST_PROFILE==='1')
export const costSpan=<T>(phase:CostPhase,site:string,f:()=>T,lock=false):T=>costMeter.run(phase,site,f,lock)
