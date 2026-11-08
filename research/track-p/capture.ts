import {mkdirSync, writeFileSync} from 'node:fs'
import {countsDump} from '../../core/counts.ts'
const dir=process.env.DUMP_DIR??'/tmp/track-p-capture';mkdirSync(dir,{recursive:true})
let serial=0, first=true
const seen=new Set<string>()
countsDump.on=(d: any)=>{
 if(!d.machine||!d.laws)return
 if(first){writeFileSync(`${dir}/family-first.json`,JSON.stringify({machine:d.machine,laws:d.laws}));first=false}
 writeFileSync(`${dir}/family.json`,JSON.stringify({machine:d.machine,laws:d.laws}))
 const key=JSON.stringify([d.law,d.pass,d.phase,d.hyps?.length])
 if(seen.has(key)||!d.hyps)return;seen.add(key)
 writeFileSync(`${dir}/stage-${serial++}.json`,JSON.stringify(d))
}
