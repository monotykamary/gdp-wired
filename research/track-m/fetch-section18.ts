// Bounded transfer of a streaming-compressed archive; never parse raw proofs here.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
const [log,vm,out]=process.argv.slice(2);if(!log||!vm||!out||!/^bx_[A-Za-z0-9]+$/.test(vm))throw Error('LOG VM OUT')
const m=readFileSync(log,'utf8').split('\n').flatMap(l=>{try{const x=JSON.parse(l);return x.artifact==='track-m-tar-v1'?[x]:[]}catch{return []}}).at(-1)
if(!m||!/^\/home\/user\/track-m-s18-receipts-[A-Za-z0-9]+$/.test(m.dir)||m.parts<1||m.parts>200)throw Error('invalid archive manifest')
const chunks:string[]=[];for(let i=0;i<m.parts;i++){const code=`console.log(JSON.stringify({part:${i},data:await Bun.file(${JSON.stringify(m.dir+'/'+i+'.txt')}).text()}))`,p=Bun.spawn(['boat','exec',vm,'--timeout','20','--json','--','bun','-e',code],{stdout:'pipe',stderr:'pipe'}),[text,err,status]=await Promise.all([new Response(p.stdout).text(),new Response(p.stderr).text(),p.exited]);if(status)throw Error(err);const e=JSON.parse(text);if(e.exitCode||e.stdoutTruncated)throw Error('failed/truncated part');const x=JSON.parse(e.stdout);if(x.part!==i)throw Error('wrong part');chunks.push(x.data)}
const bytes=Buffer.from(chunks.join(''),'base64');if(createHash('sha256').update(bytes).digest('hex')!==m.sha256)throw Error('checksum mismatch');mkdirSync(out,{recursive:true});writeFileSync(join(out,'receipts.tar.gz'),bytes);writeFileSync(join(out,'archive-manifest.json'),JSON.stringify(m,null,2)+'\n');console.log(JSON.stringify({verified:true,bytes:bytes.length,sha256:m.sha256}))
