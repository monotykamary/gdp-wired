// Transport completed receipts only; no proof search and no new VM starts.
import {existsSync,mkdirSync,readFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
const dir=process.argv[2];if(!dir)throw Error('BATCH_OUTPUT required')
const placement=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8'))
const items=Object.entries(placement).flatMap(([name,p]:[string,any])=>{
 const file=join(dir,name+'.log');if(!existsSync(file))return []
 const manifests=readFileSync(file,'utf8').split('\n').flatMap(line=>{try{const m=JSON.parse(line);return m.artifact==='track-m-tar-v1'?[m]:[]}catch{return []}})
 return manifests.length?[{name,vm:p.vm,log:file,manifest:manifests.at(-1)}]:[]
})
if(!items.length)throw Error('no completed archive manifests')
const run=async(args:string[])=>{const child=Bun.spawn(args,{stdout:'pipe',stderr:'pipe'}),[out,err,code]=await Promise.all([new Response(child.stdout).text(),new Response(child.stderr).text(),child.exited]);if(code)throw Error(args[0]+' exit '+code+': '+err+' '+out);return out.trim()}
for(let offset=0;offset<items.length;offset+=4)await Promise.all(items.slice(offset,offset+4).map(async item=>{
 const dest=join(dir,'receipts',item.name),archive=join(dest,'receipts.tar.gz'),raw=join(dest,'raw')
 if(!existsSync(archive)||createHash('sha256').update(readFileSync(archive)).digest('hex')!==item.manifest.sha256)console.log(await run(['bun','research/track-m/fetch-section18.ts',item.log,item.vm,dest]))
 const bytes=readFileSync(archive);if(bytes.length!==item.manifest.bytes||createHash('sha256').update(bytes).digest('hex')!==item.manifest.sha256)throw Error('archive mismatch '+item.name)
 mkdirSync(raw,{recursive:true});await run(['tar','-xzf',archive,'-C',raw]);console.log(JSON.stringify({name:item.name,verified:true,bytes:bytes.length,sha256:item.manifest.sha256}))
}))
