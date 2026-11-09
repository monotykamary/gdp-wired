// Research-only candidate policy, installed in disposable Linux snapshots.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux required')
const file='core/count-recovery/boolean-core.ts',s=readFileSync(file,'utf8'),anchor=' walk(g.hyps,root,(o:any)=>{\n'
if(s.split(anchor).length!==2)throw Error('nonunique selector anchor')
const extra=`
  if(extended&&o.op==='if')walkOnce(o.c,(c:any)=>{
   if(!['=','<','<='].includes(c.op))return
   let scalar=true;walkOnce([c.a,c.b],(e:any)=>{if(['get','if','sub','min','max','prod','tup','proj'].includes(e.op))scalar=false})
   if(scalar)add(c,2200)
  })`
writeFileSync(file,s.replace(anchor,anchor+extra+'\n'))
console.log(JSON.stringify({researchOnly:true,policy:'conditional-scalar-selectors'}))
