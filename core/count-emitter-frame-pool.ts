// Research-only per-emitter frame proposer. The final native certificate gate
// remains mandatory. Cached frames belong to one immutable count environment.
import {type Count,type FrameCut,canon,frameActive,frameOk,simpE,whenPath} from '../kernel/kernel.ts'
import {late} from '../kernel/prove.ts'
export class FrameFactPool {
 readonly counts:Count[]
 readonly frames:FrameCut[]
 readonly until:number
 private offered=0
 private reused=0
 private validated=0
 private rejected=0
 private removed=0
 constructor(counts:Count[],frames:FrameCut[],until:number){if(frames.length)throw Error('frame pool must start empty');this.counts=counts;this.frames=frames;this.until=until}
 private pair(f:FrameCut){return JSON.stringify([f.post,f.pre].sort())}
 offer(frame:FrameCut):boolean{
  this.offered++
  if(late(this.until))return false
  const pair=this.pair(frame),path=whenPath(frame)
  if(this.frames.some(f=>this.pair(f)===pair&&frameActive(f,path))){this.reused++;return true}
  const post=this.counts.find(c=>c.v===frame.post),pre=this.counts.find(c=>c.v===frame.pre)
  if(!post||!pre||post.key!==pre.key){this.rejected++;return false}
  const seen=new Set<string>(),all=()=>{for(const key of path.keys())seen.add(key)}
  const tracked=new Proxy(path,{get(target,key){
   if(key==='get')return (id:string)=>{const value=target.get(id);if(value!==undefined)seen.add(id);return value}
   if(key==='has')return (id:string)=>{const found=target.has(id);if(found)seen.add(id);return found}
   if(key==='size'){all();return target.size}
   if(key==='keys'||key==='values'||key==='entries'||key===Symbol.iterator||key==='forEach'){all();const value=Reflect.get(target,key,target);return value.bind(target)}
   const value=Reflect.get(target,key,target);return typeof value==='function'?value.bind(target):value
  }})
  const equal=(a:unknown,b:unknown)=>JSON.stringify(a)===JSON.stringify(b)
  const same=equal(simpE(post.below,tracked,post.key),simpE(pre.below,tracked,pre.key))&&equal(simpE(post.body,tracked,post.key),simpE(pre.body,tracked,pre.key))
  const short={...frame,when:frame.when.filter(row=>seen.has(canon(row)))}
  let candidate=frame
  if(same){this.validated++;if(frameOk(this.counts,short))candidate=short;else{this.validated++;if(!frameOk(this.counts,frame)){this.rejected++;return false}}}
  else{this.validated++;if(!frameOk(this.counts,frame)){this.rejected++;return false}}
  const keys=new Set(candidate.when.map(canon))
  for(let i=this.frames.length-1;i>=0;i--){const old=this.frames[i]!;if(this.pair(old)===pair&&[...keys].every(k=>old.when.some(row=>canon(row)===k))){this.frames.splice(i,1);this.removed++}}
  this.frames.push(candidate)
  return true
 }
 stats(){return {offered:this.offered,reused:this.reused,validated:this.validated,rejected:this.rejected,removed:this.removed,frames:this.frames.length,guards:this.frames.reduce((n,f)=>n+f.when.length,0)}}
}
