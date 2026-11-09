import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {brotliDecompressSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {basename} from 'node:path'
const root=process.argv[2]??'runs/mldr-incl-capture-v1',name=process.argv[3]??'capture.log',out=process.argv[4]??root+'/files'
const row=readFileSync(root+'/'+name,'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>{try{return JSON.parse(l)}catch{return {}}}).find(r=>r.artifact==='mldr-incl-capture')
if(!row)throw Error('capture archive missing');const bytes=Buffer.from(row.data,'base64');if(createHash('sha256').update(bytes).digest('hex')!==row.sha256)throw Error('capture hash')
mkdirSync(out,{recursive:true});const files=JSON.parse(brotliDecompressSync(bytes).toString()) as Record<string,string>
for(const [name,text]of Object.entries(files)){if(basename(name)!==name)throw Error('unsafe name');writeFileSync(out+'/'+name,text)}
console.log(JSON.stringify({files:Object.keys(files).length,omitted:row.omitted,sha256:row.sha256,stages:Object.entries(files).filter(([n])=>n.startsWith('stage-')).map(([name,text])=>{const d=JSON.parse(text);return {name,law:d.law,pass:d.pass,phase:d.phase,hyps:d.hyps?.length,reads:d.certificateRequest?.reads?.length}})}))
