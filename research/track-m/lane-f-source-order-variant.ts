// Disposable source-order comparison. No candidate, premise, or deadline is added.
import {readFileSync,writeFileSync,renameSync} from 'node:fs'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux required')
const mode=process.argv[2]
if(mode!=='compensated'&&mode!=='ready-empty')throw Error('compensated | ready-empty')
const file='core/count-recovery/derivability-closure.ts',source=readFileSync(file,'utf8')
const importBefore="import {shadowedTransportIndices} from '../../research/track-m/prefer-compensated.ts'"
const anchor=' const shadowed=shadowedTransportIndices(cert)'
const pending='new Set(violated.filter(i=>!excluded.has(i)))'
for(const text of [importBefore,anchor,pending])if(source.split(text).length!==2)throw Error('source-order anchor changed')
const empty=mode==='ready-empty'?`
  const q=cert.insts[index]!,id=q.unit===0&&q.terms.length===1&&q.terms[0]![0]===1?q.terms[0]![1]:undefined
  if(id){
   if(!countBodies.has(id)){const read=cert.reads.find(r=>r[0]===id);countBodies.set(id,read?countsForReads(ds,[read])?.[0]?.body:undefined)}
   const aliases:Record<string,E>={}
   for(const [a,b]of pairs)if(a.op==='var'&&truth({op:'=',a,b},path)===true)aliases[a.name]=b
   const body=countBodies.get(id)
   if(body&&emptyCountSource(body,aliases))return Math.min(prior,-0.75)
  }`:''
const extra=` const compensated=compensatedTransportIndices(cert)
 const rankAt=(index:number,path:Path):number=>{
  const prior=rank(index)${empty}
  return compensated.has(index)?Math.min(prior,-0.5):prior
 }
 trace.push({stage:'closure-source-order',mode:'${mode}'})
`
// In the non-scope variant retain the same signature without an unused argument.
const ranked=mode==='ready-empty'?extra:extra.replace('(index:number,path:Path)','(index:number)')
const order=mode==='ready-empty'?'rankAt(a,scope)-rankAt(b,scope)':'rankAt(a)-rankAt(b)'
const next=source.replace(importBefore,"import {compensatedTransportIndices,shadowedTransportIndices} from '../../research/track-m/prefer-compensated.ts'")
 .replace(anchor,ranked+anchor).replace(pending,`new Set(violated.filter(i=>!excluded.has(i)).sort((a,b)=>${order}))`)
writeFileSync(file+'.tmp',next);renameSync(file+'.tmp',file)
