// Bounded, checksum-verified retrieval. Extract only explicitly requested files.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join,basename} from 'node:path'
import {createHash} from 'node:crypto'
import {brotliDecompressSync} from 'node:zlib'
const [log,vm,out,...wanted]=process.argv.slice(2);if(!log||!vm||!out||!/^bx_[A-Za-z0-9]+$/.test(vm))throw new Error('LOG VM OUT [FILES] required')
const m=readFileSync(log,'utf8').split('\n').flatMap(l=>{try{const x=JSON.parse(l);return x.artifact==='section10-chunk-manifest'?[x]:[]}catch{return []}}).at(-1)
if(!m||!/^\/home\/user\/track-m-s10-receipts-[A-Za-z0-9]+$/.test(m.dir)||!Number.isInteger(m.parts)||m.parts<1||m.parts>100)throw new Error('missing/invalid archive manifest')
const chunks:string[]=[]
for(let i=0;i<m.parts;i++){
 const script=`console.log(JSON.stringify({part:${i},data:await Bun.file(${JSON.stringify(m.dir+'/'+i+'.txt')}).text()}))`,p=Bun.spawn(['boat','exec',vm,'--timeout','20','--json','--','bun','-e',script],{stdout:'pipe',stderr:'pipe'})
 const [text,err,code]=await Promise.all([new Response(p.stdout).text(),new Response(p.stderr).text(),p.exited]);if(code)throw new Error(err);const e=JSON.parse(text);if(e.exitCode||e.stdoutTruncated)throw new Error('part failed/truncated');const part=JSON.parse(e.stdout);if(part.part!==i)throw new Error('wrong part');chunks.push(part.data)
}
const bytes=Buffer.from(chunks.join(''),'base64');if(createHash('sha256').update(bytes).digest('hex')!==m.sha256)throw new Error('archive hash mismatch');mkdirSync(out,{recursive:true});writeFileSync(join(out,'receipts.br'),bytes);writeFileSync(join(out,'archive-manifest.json'),JSON.stringify(m,null,2)+'\n')
const files=JSON.parse(brotliDecompressSync(bytes).toString());for(const name of wanted){if(name!==basename(name)||typeof files[name]!=='string')throw new Error('invalid extraction '+name);writeFileSync(join(out,name),files[name])}
console.log(JSON.stringify({verified:true,sha256:m.sha256,extracted:wanted,bytes:bytes.length}))
