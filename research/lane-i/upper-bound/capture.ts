// Research only: observe the unchanged original entry point's admission family.
import {mkdirSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {brotliCompressSync} from 'node:zlib'
import {countsDump} from '../../../core/counts.ts'
const hash=(s:string)=>createHash('sha256').update(s).digest('hex')
countsDump.on=e=>{
 const v=e as any;if(v.phase!=='original-family')return
 const laws:any[]=v.laws,candidates:any[]=v.candidateLaws
 if(laws.length!==34||candidates.length!==34)throw Error(`expected original 34-law family, got ${laws.length}/${candidates.length}`)
 const names={star:'inX: no quorum canVote/3',half:'inX: stored guard reconfigs/inS or disabled/0',rows:'fields: CV[a]=CV[b] and CfgT[a]=CfgT[b] -> Config rows agree',p1:'count cubes: every x with x < {"op":"var","name":"size"}: never CV[x] is 0 and 1 <= inX$row[x]',safety:'one primary per term'}
 const targets=Object.fromEntries(Object.entries(names).map(([tag,name])=>{const hits=laws.flatMap((l,i)=>l.name===name?[i]:[]);if(hits.length!==1)throw Error(`target ${tag}: ${hits.length} matches`);return[tag,hits[0]]}))
 const indices=(xs:any[])=>xs.map(l=>{const i=laws.indexOf(l);if(i<0)throw Error('family member lost');return i})
 const data={researchOnly:true,source:'original run.ts post-finite admission callback',sourceSha:process.env.UPPER_SOURCE_SHA,originalHarness:true,generatorOnly:true,suppliedLaws:[],m:v.machine,laws,caller:indices(v.caller),support:indices([...v.support]),targets,candidateCount:candidates.length,machineSha256:hash(JSON.stringify(v.machine)),lawsSha256:hash(JSON.stringify(laws))}
 const text=JSON.stringify(data);mkdirSync('upper-capture',{recursive:true});writeFileSync('upper-capture/family.json',text)
 console.log('UPPER_FAMILY '+JSON.stringify({sha256:hash(text),data:brotliCompressSync(Buffer.from(text)).toString('base64')}))
 throw Error('UPPER_ORIGINAL_FAMILY_CAPTURED')
}
