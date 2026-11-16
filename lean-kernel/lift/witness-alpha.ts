// Syntactic preflight only. Equivalence is established by QAlpha/RowAlpha in
// emitted Lean, never by this proposal or by equality of hashes alone.
import {createHash} from 'node:crypto'
import {isDeepStrictEqual} from 'node:util'
import type {C,Machine} from '../../core/machine.ts'
import {substC,substE} from '../../kernel/kernel.ts'
import {alphaProposals,rowAlphaProposals} from './source-projection.ts'
export type WitnessAlpha={sourceSha256:string,producerSourceSha256:string,renames:ReturnType<typeof alphaProposals>,rows:ReturnType<typeof rowAlphaProposals>}
const sha=(m:Machine):string=>createHash('sha256').update(JSON.stringify(m)).digest('hex')
export function proposeWitnessAlpha(source:Machine,producer:Machine):WitnessAlpha|undefined {
  if(isDeepStrictEqual(source,producer)&&sha(source)===sha(producer))return undefined
  const renames=alphaProposals(source,producer),rows=rowAlphaProposals(source,producer)
  let renamed=source
  const flags:Record<string,C>=Object.fromEntries(Object.keys(source.step.flags??{}).map(name=>[name,{op:'flag',name}]))
  const sub=(old:string,fresh:string)=>({vars:{[old]:{op:'var' as const,name:fresh}},maps:{},flags})
  for(const r of renames){
    const q=renamed.step.flags?.[r.flag]
    if(q?.op!=='all')throw Error('missing quantified alpha source')
    const next={...q,key:q.key===r.old?r.fresh:q.key,...(q.keys?{keys:q.keys.map(k=>k===r.old?r.fresh:k)}:{}),c:substC(q.c,sub(r.old,r.fresh))}
    renamed={...renamed,step:{...renamed.step,flags:{...renamed.step.flags,[r.flag]:next}}}
  }
  for(const r of rows){
    const w=renamed.step.maps?.[r.map]
    if(!w||!('each'in w))throw Error('missing row alpha source')
    renamed={...renamed,step:{...renamed.step,maps:{...renamed.step.maps,[r.map]:{...w,each:r.fresh,value:substE(w.value,sub(r.old,r.fresh))}}}}
  }
  if((!renames.length&&!rows.length)||!isDeepStrictEqual(renamed,producer))throw Error('witness source differs beyond bound-name alpha conversion')
  return {sourceSha256:sha(source),producerSourceSha256:sha(producer),renames,rows}
}
