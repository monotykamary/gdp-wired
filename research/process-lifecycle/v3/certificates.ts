import {readFileSync,existsSync,readdirSync,writeSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {deflateRawSync} from 'node:zlib'
import {checkDocument} from '../../../interchange/check.ts'
const sha=(x:Buffer|string)=>createHash('sha256').update(x).digest('hex')
const need=(x:unknown,m:string)=>{if(!x)throw Error(m)}
function emit(x:unknown){const b=Buffer.from(JSON.stringify(x)+'\n');let n=0;while(n<b.length)n+=writeSync(1,b.subarray(n))}
const manifest=JSON.parse(readFileSync('review-input/input-manifest.json','utf8'))
const sourcePath='research/process-lifecycle/model.py',lines=readFileSync(sourcePath,'utf8').split('\n')
const expected=lines.flatMap((line,i)=>{const m=line.match(/^\s*# gdp: law (.*?): (.*)$/);if(!m)return [];const [,name,expr]=m;if(name===undefined||expr===undefined)throw Error('invalid law annotation capture');return [{name,expr,where:sourcePath+':'+(i+1)}]})
need(expected.length===9,'wrong unchanged law count')
const dir='work/certs',files=existsSync(dir)?readdirSync(dir).filter(f=>f.endsWith('.json')).sort():[]
const accepted=new Set<string>();let failed=false
for(const file of files){
 const raw=readFileSync(dir+'/'+file);let verdict:any
 try{const doc=JSON.parse(raw.toString()),law=expected.find(l=>l.name===doc.meta?.law)
  if(!law)throw Error('certificate/source binding mismatch')
  need(doc.meta.expr===law.expr&&doc.meta.where===law.where&&doc.meta.file===sourcePath&&doc.meta.entry==='Lifecycle','certificate/source binding mismatch')
  need(!accepted.has(law.name),'duplicate certificate')
  const checked=checkDocument(doc);need(checked.accepted&&checked.claims.some(c=>c.name===law.name&&c.accepted),'certificate refused')
  accepted.add(law.name);verdict={accepted:true,law:law.name,checked}
 }catch(e){failed=true;verdict={accepted:false,error:String(e)}}
 emit({event:'certificate',file,sha256:sha(raw),bytes:raw.length,encoding:'deflate-raw/base64',data:deflateRawSync(raw).toString('base64'),...verdict})
}
for(const f of manifest.inputs)need(sha(readFileSync(f.path))===f.sha256,'input changed '+f.path)
const ok=!failed&&accepted.size===9&&files.length===9
emit({event:'certificate-summary',accepted:ok,certificateCount:files.length,acceptedLawCount:accepted.size,acceptedLaws:[...accepted],inputsUnchanged:true})
process.exitCode=ok?0:2
