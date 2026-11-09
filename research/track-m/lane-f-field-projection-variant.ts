// Disposable experiment: retain existing primitive-field premises in Phase C.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux required')
const path='core/count-recovery/derivability-closure.ts',s=readFileSync(path,'utf8'),from="if(o.op==='get'||o.op==='var'&&wits.has(o.name))other=true",to="if(o.op==='get'&&maps.has(o.map)||o.op==='var'&&wits.has(o.name))other=true"
if(s.split(from).length!==2)throw Error('projection anchor changed')
writeFileSync(path,s.replace(from,to))
