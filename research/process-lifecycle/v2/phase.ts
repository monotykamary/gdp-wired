import {readFileSync,existsSync,mkdirSync,readdirSync,writeSync} from 'node:fs'
import {execFileSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {deflateRawSync} from 'node:zlib'
const sha=(x:Buffer|string)=>createHash('sha256').update(x).digest('hex')
const need=(x:unknown,m:string)=>{if(!x)throw Error(m)}
function emit(x:unknown){const b=Buffer.from(JSON.stringify(x)+'\n');let n=0;while(n<b.length)n+=writeSync(1,b.subarray(n))}
const manifest=JSON.parse(readFileSync('review-input/input-manifest.json','utf8'))
function unchanged(){for(const f of manifest.inputs)need(sha(readFileSync(f.path))===f.sha256,'input changed '+f.path)}
if(process.argv[2]==='setup'){
 unchanged()
 const archive=readFileSync('review-input/typescript-5.9.3.tgz')
 need('sha512-'+createHash('sha512').update(archive).digest('base64')===manifest.typescript.integrity,'archive integrity')
 need(!existsSync('node_modules'),'refuse pre-existing unpinned node_modules')
 mkdirSync('node_modules/typescript',{recursive:true})
 execFileSync('tar',['-xzf','review-input/typescript-5.9.3.tgz','--strip-components=1','-C','node_modules/typescript'],{timeout:2000})
 const p=JSON.parse(readFileSync('node_modules/typescript/package.json','utf8'))
 need(p.version==='5.9.3'&&Object.keys(p.dependencies??{}).length===0,'unexpected runtime dependency closure')
 const ts=await import('typescript');need(ts.default.version==='5.9.3','wrong loaded TypeScript')
 emit({event:'setup-verified',inputs:manifest.inputs.length,typescriptVersion:p.version,archiveSha256:sha(archive),typescriptMainSha256:sha(readFileSync('node_modules/typescript/lib/typescript.js')),networkInstall:false,autoInstall:false})
}else if(process.argv[2]==='certificates'){
 const {checkDocument}=await import('../../../interchange/check.ts')
 const sourcePath='research/process-lifecycle/model.py',lines=readFileSync(sourcePath,'utf8').split('\n')
 const expected=lines.flatMap((line,i)=>{const m=line.match(/^\s*# gdp: law (.*?): (.*)$/);return m?[{name:m[1],expr:m[2],where:sourcePath+':'+(i+1)}]:[]})
 need(expected.length===9,'wrong unchanged law count')
 const dir='lifecycle-v2-work/certs',files=existsSync(dir)?readdirSync(dir).filter(f=>f.endsWith('.json')).sort():[]
 const accepted=new Set<string>();let failed=false
 for(const file of files){
  const raw=readFileSync(dir+'/'+file);let verdict:any
  try{const doc=JSON.parse(raw.toString()),law=expected.find(l=>l.name===doc.meta?.law)
   need(law&&doc.meta.expr===law.expr&&doc.meta.where===law.where&&doc.meta.file===sourcePath&&doc.meta.entry==='Lifecycle','certificate/source binding mismatch')
   need(!accepted.has(law.name),'duplicate certificate')
   const checked=checkDocument(doc);need(checked.accepted&&checked.claims.some(c=>c.name===law.name&&c.accepted),'certificate refused')
   accepted.add(law.name);verdict={accepted:true,law:law.name,checked}
  }catch(e){failed=true;verdict={accepted:false,error:String(e)}}
  emit({event:'certificate',file,sha256:sha(raw),bytes:raw.length,encoding:'deflate-raw/base64',data:deflateRawSync(raw).toString('base64'),...verdict})
 }
 unchanged()
 const ok=!failed&&accepted.size===9&&files.length===9
 emit({event:'certificate-summary',accepted:ok,certificateCount:files.length,acceptedLawCount:accepted.size,acceptedLaws:[...accepted],inputsUnchanged:true})
 process.exitCode=ok?0:2
}else throw Error('unknown phase')
