// Census retained accepted objects; no search and no certificate mutation.
import {readFileSync,readdirSync,mkdtempSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {tmpdir} from 'node:os'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
const root=process.argv[2]??'evidence', sha=(s:string)=>createHash('sha256').update(s).digest('hex')
const parse=(s:string):any[]=>s.split('\n').flatMap(l=>{try{return[JSON.parse(l)]}catch{return[]}})
const metaText=readFileSync(join(root,'capture-metadata-final/capture-metadata.log'),'utf8'), metas=parse(metaText).filter(r=>r.captureSha256)
const rows:any[]=[]
console.log('CENSUS_SCRIPT_SHA256',sha(readFileSync('research/verify-all/paxos-feature-census.ts','utf8')))
console.log('METADATA_LOG_SHA256',sha(metaText))
for(const file of readdirSync(join(root,'capture-all')).filter(f=>f.endsWith('.log')).sort()){
 const text=readFileSync(join(root,'capture-all',file),'utf8'), packed=text.match(/ARCHIVE_BEGIN\n([A-Za-z0-9+/=\r\n]+)\nARCHIVE_END/)
 if(!packed)throw Error('missing packet '+file)
 const dir=mkdtempSync(join(tmpdir(),'paxos-census-')), archive=join(dir,'packet.tar.xz')
 writeFileSync(archive,Buffer.from(packed[1]!,'base64'))
 const t=spawnSync('tar',['-xJf',archive,'-C',dir],{encoding:'utf8',timeout:30000});if(t.status!==0)throw Error(t.stderr)
 const name=readdirSync(dir).find(f=>f.endsWith('.json')&&!f.endsWith('.result.json'))!
 const raw=readFileSync(join(dir,name),'utf8'), x=JSON.parse(raw,(_k,v)=>v?.__map?new Map(v.__map):v?.__set?new Set(v.__set):v)
 const id=x.row.id, meta=metas.find(r=>r.id===id);if(!meta||meta.captureSha256!==sha(raw))throw Error('packet identity mismatch '+id)
 const accepted=!!(x.verdict.out.proven&&x.verdict.out.checked), c=x.counted?.checked?x.counted:x.good
 const base=parse(text).find(r=>r.captureSha256)
 let exit=text.match(/LEAN_EXIT (\d+)/)?.[1],leanSha=base?.leanSha256,packetSha=base?.captureSha256,receipt='capture-all/'+file,receiptText=text
 for(const batch of ['recheck-capture','recheck-final']){
  const path=join(root,batch,'recheck-'+id+'.log')
  let content:string;try{content=readFileSync(path,'utf8')}catch{continue}
  const rs=parse(content), out=rs.find(r=>r.captureSha256), checked=rs.find(r=>r.leanExit!==undefined)
  if(checked){exit=String(checked.leanExit);leanSha=out?.leanSha256;packetSha=out?.captureSha256;receipt=batch+'/recheck-'+id+'.log';receiptText=content}
 }
 const laws:any[]=accepted?c.laws:[], flags=Object.entries(c?.machine?.step?.flags??{}).filter(([,v]:any)=>v?.op==='all') as [string,any][]
 const detail=(l:any,index:number)=>({index,name:l.name,forall:l.forall??null,keys:l.keys??[],flagBinderCollisions:(l.keys??[]).flatMap((k:string)=>flags.filter(([,f])=>[f.key,...(f.keys??[])].includes(k)).map(([flag])=>({key:k,flag}))),startCertificate:!!c.proof?.certs?.[l.name+' @start'],stepCertificate:!!c.proof?.certs?.[l.name+' @step']})
 const indexed=laws.map(detail), scan=indexed.filter(l=>l.name.startsWith('scan-prefix:')&&l.keys.length>0), carry=indexed.filter(l=>l.name.startsWith('carry:co-write:')), further=indexed.filter(l=>l.keys.length>0)
 const checked=accepted&&exit==='0'&&packetSha===meta.captureSha256&&leanSha===meta.leanSha256
 if(accepted&&id!=='paxos_epr'&&!checked)throw Error('missing matching accepted Lean receipt '+id)
 const row={id,accepted,kind:meta.kind??null,packetSha256:meta.captureSha256,leanSha256:meta.leanSha256??null,leanChecked:checked,leanExit:exit??null,receipt,receiptSha256:sha(receiptText),lawCount:laws.length,scanPrefixFurtherKeys:scan,carryCoWrite:carry,otherFurtherKeys:further.filter(l=>!scan.includes(l))}
 rows.push(row);console.log('CENSUS_ROW',JSON.stringify(row))
}
if(rows.length!==29||rows.filter(r=>r.accepted).length!==28||rows.filter(r=>r.accepted&&r.id!=='paxos_epr'&&r.leanChecked).length!==27)throw Error('unexpected census totals')
const others=rows.filter(r=>r.accepted&&r.id!=='paxos_epr')
console.log('CENSUS_SUMMARY',JSON.stringify({rows:rows.length,accepted:28,otherAccepted:others.length,otherLeanChecked:others.filter(r=>r.leanChecked).length,otherScanPrefix:others.filter(r=>r.scanPrefixFurtherKeys.length).map(r=>r.id),otherCarryCoWrite:others.filter(r=>r.carryCoWrite.length).map(r=>r.id),otherCollisions:others.filter(r=>[...r.scanPrefixFurtherKeys,...r.otherFurtherKeys].some((l:any)=>l.flagBinderCollisions.length)).map(r=>r.id),censusSha256:sha(JSON.stringify(rows))}))
