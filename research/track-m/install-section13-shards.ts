import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw new Error('disposable Linux copy required')
const manifest:any[]=[],hash=(s:string)=>createHash('sha256').update(s).digest('hex')
const change=(file:string,fn:(s:string)=>string)=>{const before=readFileSync(file,'utf8'),after=fn(before);writeFileSync(file,after);manifest.push({file,before:hash(before),after:hash(after)})}
const replace=(s:string,a:string,b:string)=>{if(s.split(a).length!==2)throw new Error('nonunique anchor '+a);return s.replace(a,b)}
change('core/count-focus-proof.ts',s=>"import {shardControl as __s} from '../research/track-m/section13-control.ts'\n"+replace(s,'for(const carried of [undefined,...m.inputMaps]){',"for(const carried of [undefined,...m.inputMaps]){\n    __s.context={carried:carried??null,targets:!targetCounts?rows:undefined}"))
change('core/count-cases.ts',s=>{
 s="import {shardControl as __s} from '../research/track-m/section13-control.ts'\n"+s
 s=replace(s,'  let goal:Goal={...root,name:packet.goal.name}',"  let goal:Goal={...root,name:packet.goal.name}\n  __s.capture({m,laws,at,cert,packet,options,context:__s.context})")
 s=replace(s,'      branches.push({prefix,path:new Map(path),root,tails})',`      branches.push({prefix,path:new Map(path),root,tails})
      if(__s.mode==='run'&&value!==__s.op){
       records.push(undefined);for(const v of tails)path.delete(canon(splitAt(v)))
       if(split){path.set(canon(split),{lin:split,holds:false});conditions.push({op:'not',x:cut!})}
       continue
      }`)
 s=replace(s,'      records.push(tree&&source?{goal:source,tree,path:new Map(path),indices,...(from?{from}:{})}:undefined)',"      records.push(tree&&source?{goal:source,tree,path:new Map(path),indices,...(from?{from}:{})}:undefined)\n      __s.finish(records.at(-1),{goal,packet,at,cert,path:new Map(path)})")
 return s
})
change('core/count-recovery/derivability-closure.ts',s=>{
 s="import {shardControl as __s} from '../../research/track-m/section13-control.ts'\n"+s
 const queries=[
  ["__d.run('natural-query',{},()=>proveNaturalCases(numeric,scope,end,trace,{deferCheck:true}))","{kind:'natural',goal:numeric,path:[...scope],closure:__closure.id}"],
  ["__d.run('numeric-query',{},()=>modelSequence(scope)(numeric,end))","{kind:'numeric',goal:numeric,path:[...scope],closure:__closure.id}"],
  ["__d.run('batch-query',{indices},()=>modelSequence(scope)(assumed,end))","{kind:'batch',indices,goal:assumed,path:[...scope],closure:__closure.id}"],
  ["__d.run('source-query',{index,limit:queryLimit},()=>modelSequence(path)(part,queryLimit))","{kind:'source',index,goal:part,path:[...path],closure:__closure.id}"]
 ]
 for(const [call,packet]of queries)s=replace(s,call!,`__s.query(${packet},()=>${call})`)
 return s
})
console.log(JSON.stringify({diagnosticInstall:'section13-shards',manifest}))
