// Diagnostic T1 sub-attribution. No prover queries or proof edits.
import {census,type Phase} from './phase-census-meter.ts'
import {followup} from './section7-followup-meter.ts'
export {followup}
type Frame={site:string,kind:string,start:number,phases:Record<string,number>,caller:string}
type Stat={calls:number,wallMs:number,phases:Record<string,number>}
class DetailMeter {
 enabled=process.env.LAB_SECTION7_T1==='1'
 label=''
 private stack:Frame[]=[]
 private sites:Record<string,Stat>={}
 private buckets:Record<string,Record<string,number>>={}
 private checkCalls:{caller:string,hyps:number,root:string,wallMs:number}[]=[]
 reset(label:string){if(this.stack.length)throw new Error('detail frames left open');this.label=label;this.sites={};this.buckets={};this.checkCalls=[];followup.reset(label)}
 observe(phase:Phase,ms:number){if(!this.enabled)return;for(const frame of this.stack)frame.phases[phase]=(frame.phases[phase]??0)+ms;const kind=this.stack.some(f=>f.kind==='admission')?'admission':this.stack.some(f=>f.kind==='transport')?'transport':this.stack.at(-1)?.kind??'other';const row=this.buckets[phase]??={};row[kind]=(row[kind]??0)+ms}
 begin(site:string,kind:string){if(!this.enabled)return undefined;census.snapshot();const frame:Frame={site,kind,start:performance.now(),phases:{},caller:this.stack.at(-1)?.site??'outside'};this.stack.push(frame);return frame}
 end(frame:Frame|undefined){if(!frame)return;census.snapshot();while(this.stack.length){const top=this.stack.pop()!,wallMs=performance.now()-top.start,stat=this.sites[top.site]??={calls:0,wallMs:0,phases:{}};stat.calls++;stat.wallMs+=wallMs;for(const [phase,n]of Object.entries(top.phases))stat.phases[phase]=(stat.phases[phase]??0)+n;if(top===frame)break}}
 run<T>(site:string,kind:string,f:()=>T):T{const frame=this.begin(site,kind);try{return f()}finally{this.end(frame)}}
 kernel<T>(site:string,args:any[],f:()=>T):T{if(!this.enabled)return f();const caller=this.stack.at(-1)?.site??'outside',start=performance.now();try{return this.run(site,'kernel',f)}finally{followup.record(args,caller);this.checkCalls.push({caller,hyps:args[0]?.hyps?.length??-1,root:args[1]&&'leaf'in args[1]?'leaf':'split',wallMs:performance.now()-start})}}
 withLeafContext<T>(goal:any,tree:any,path:any,lemmas:any[],f:()=>T):T{return followup.withLeafContext(goal,tree,path,lemmas,f)}
 capture(){followup.seal();if(this.stack.length)throw new Error('detail capture during proof');const checks:Record<string,{calls:number,wallMs:number,minHyps:number,maxHyps:number,leaf:number}>={};for(const c of this.checkCalls){const s=checks[c.caller]??={calls:0,wallMs:0,minHyps:Infinity,maxHyps:0,leaf:0};s.calls++;s.wallMs+=c.wallMs;s.minHyps=Math.min(s.minHyps,c.hyps);s.maxHyps=Math.max(s.maxHyps,c.hyps);if(c.root==='leaf')s.leaf++}return JSON.parse(JSON.stringify({label:this.label,buckets:this.buckets,sites:this.sites,checks}))}
}
export const detail=new DetailMeter()
census.onSlice=(phase,ms)=>detail.observe(phase,ms)
