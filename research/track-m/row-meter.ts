// Diagnostic only: the production rowsAt never imports this module.
import type {Goal,Path} from '../../kernel/kernel.ts'
type Entry={keys:Set<string>,structural:string,name:string,calls:number,ms:number}
export class RowMeter{
 private goals=new WeakMap<Goal,Entry>();private entries:Entry[]=[]
 private structural=new Map<string,Set<string>>()
 calls=0;ms=0;repeatCalls=0;repeatMs=0;prefixCalls=0;prefixMs=0;crossGoalCalls=0;distinct=0;rows=0;maxMs=0
 constructor(readonly enabled=false,private now=()=>performance.now()){}
 run<T extends {length:number}>(goal:Goal,path:Path,fn:()=>T):T{
  if(!this.enabled)return fn()
  let entry=this.goals.get(goal)
  if(!entry){entry={keys:new Set(),structural:JSON.stringify(goal.hyps),name:goal.name,calls:0,ms:0};this.goals.set(goal,entry);this.entries.push(entry)}
  const atoms=[...path].map(([id,a])=>JSON.stringify([id,a.holds])),key=JSON.stringify(atoms),repeat=entry.keys.has(key)
  let prefix=false
  for(let i=atoms.length-1;i>=0&&!prefix;i--)prefix=entry.keys.has(JSON.stringify(atoms.slice(0,i)))
  let shared=this.structural.get(entry.structural)
  if(!shared)this.structural.set(entry.structural,(shared=new Set()))
  if(!repeat&&shared.has(key))this.crossGoalCalls++
  const start=this.now();const out=fn();const ms=this.now()-start
  this.calls++;this.ms+=ms;this.maxMs=Math.max(this.maxMs,ms);this.rows+=out.length;entry.calls++;entry.ms+=ms
  if(repeat){this.repeatCalls++;this.repeatMs+=ms}else{entry.keys.add(key);shared.add(key);this.distinct++;if(prefix){this.prefixCalls++;this.prefixMs+=ms}}
  return out
 }
 snapshot(){return {enabled:this.enabled,calls:this.calls,goalIdentities:this.entries.length,structuralGoals:this.structural.size,distinctOrderedKeys:this.distinct,repeatCalls:this.repeatCalls,repeatMs:this.repeatMs,prefixCalls:this.prefixCalls,prefixMs:this.prefixMs,crossGoalCalls:this.crossGoalCalls,ms:this.ms,meanMs:this.calls?this.ms/this.calls:0,maxMs:this.maxMs,meanRows:this.calls?this.rows/this.calls:0,topGoals:this.entries.toSorted((a,b)=>b.ms-a.ms).slice(0,8).map(e=>({name:e.name,calls:e.calls,keys:e.keys.size,ms:e.ms}))}}
}
export const rowMeter=new RowMeter(process.env.TRACK_M_ROWS_PROFILE==='1')
export const rowCall=<T extends {length:number}>(goal:Goal,path:Path,f:()=>T):T=>rowMeter.run(goal,path,f)
