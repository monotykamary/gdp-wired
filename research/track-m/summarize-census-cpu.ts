// Compact CPU-profile receipts before the remote stdout retention limit.
import {readdirSync,readFileSync,writeFileSync} from 'node:fs'
import {join,basename} from 'node:path'
import {createHash} from 'node:crypto'
const dir=process.argv[2];if(!dir)throw new Error('profile directory required')
for(const file of readdirSync(dir).filter(p=>p.endsWith('.cpuprofile'))){
 const bytes=readFileSync(join(dir,file)),p=JSON.parse(bytes.toString('utf8'))
 const nodes=new Map<number,any>(p.nodes.map((n:any)=>[n.id,n])),parents=new Map<number,number>()
 for(const n of p.nodes)for(const child of n.children??[])parents.set(child,n.id)
 const key=(n:any)=>`${n.callFrame.functionName||'(anon)'}@${basename(n.callFrame.url||'(native)')}:${n.callFrame.lineNumber+1}`
 const self=new Map<string,number>(),inclusive=new Map<string,number>(),kernelSelf=new Map<string,number>()
 let sampledUs=0,kernelUs=0,gcUs=0
 for(let i=0;i<p.samples.length;i++){
  const id=p.samples[i],delta=p.timeDeltas[i]??0,n=nodes.get(id)
  if(!n)throw new Error('missing profile node')
  sampledUs+=delta;const own=key(n),seen=new Set<string>();let kernel=false
  self.set(own,(self.get(own)??0)+delta)
  if(/garbage|\(gc\)/i.test(own))gcUs+=delta
  for(let at:number|undefined=id;at!==undefined;at=parents.get(at)){
   const node=nodes.get(at),k=key(node)
   if(node.callFrame.url?.endsWith('/kernel/kernel.ts')&&/check/.test(node.callFrame.functionName))kernel=true
   if(!seen.has(k)){seen.add(k);inclusive.set(k,(inclusive.get(k)??0)+delta)}
  }
  if(kernel){kernelUs+=delta;kernelSelf.set(own,(kernelSelf.get(own)??0)+delta)}
 }
 const top=(map:Map<string,number>)=>[...map].sort((a,b)=>b[1]-a[1]).slice(0,40).map(([name,us])=>({name,ms:us/1000}))
 const result={file,sha256:createHash('sha256').update(bytes).digest('hex'),bytes:bytes.length,nodes:p.nodes.length,samples:p.samples.length,profileWallMs:(p.endTime-p.startTime)/1000,sampledMs:sampledUs/1000,kernelMs:kernelUs/1000,gcMs:gcUs/1000,self:top(self),inclusive:top(inclusive),kernelSelf:top(kernelSelf),note:'Sampling evidence, not an exclusive wall meter. Full profiles omitted from stdout to preserve bounded receipts.'}
 writeFileSync(join(dir,file+'.summary.json'),JSON.stringify(result,null,2)+'\n')
}
