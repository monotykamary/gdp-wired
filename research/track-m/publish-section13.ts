// Observe scheduler files, not a second poller. Recover bounded log tails by
// fetching the completed job's checksum-protected archive before publication.
import {watch,existsSync,readFileSync,writeFileSync,renameSync,mkdirSync} from 'node:fs'
import {join,basename} from 'node:path'
import {homedir} from 'node:os'
import {createHash} from 'node:crypto'
import {brotliDecompressSync} from 'node:zlib'
import {normalizeSection13} from './normalize-section13.ts'
const [runLog='',out='',runOut='']=process.argv.slice(2);if(!runLog||!out||!runOut)throw new Error('RUN_LOG OUT RUN_OUT required')
mkdirSync(out,{recursive:true})
const queue=join(homedir(),'.local/share/supercomputer/live/scheduler/queue'),published=new Set<string>(),working=new Set<string>(),watchers:ReturnType<typeof watch>[]=[]
let batch:string|undefined,busy=false,again=false
const jobs=[...Array.from({length:4},(_,i)=>`star-op${i+3}`),...Array.from({length:7},(_,i)=>`overlap-op${i}`)]
const put=(path:string,text:string)=>{writeFileSync(path+'.tmp',text);renameSync(path+'.tmp',path)}
const finish=()=>{for(const w of watchers)w.close();clearTimeout(deadline);console.log(JSON.stringify({complete:true,published:published.size,batch}))}
async function archive(job:string,row:any,manifest:any){
 if(!/^bx_[A-Za-z0-9]+$/.test(row.vm)||!/^\/home\/user\/track-m-s10-receipts-[A-Za-z0-9]+$/.test(manifest.dir)||!Number.isInteger(manifest.parts)||manifest.parts<1||manifest.parts>100)throw new Error('invalid archive receipt')
 const saved=join(runOut,job,'result.json'),savedArchive=join(runOut,job,'receipts.br')
 if(existsSync(saved)&&existsSync(savedArchive)&&createHash('sha256').update(readFileSync(savedArchive)).digest('hex')===manifest.sha256)return JSON.parse(readFileSync(saved,'utf8'))
 const chunks:string[]=[]
 for(let i=0;i<manifest.parts;i++){
  const script=`console.log(JSON.stringify({part:${i},data:await Bun.file(${JSON.stringify(manifest.dir+'/'+i+'.txt')}).text()}))`
  const child=Bun.spawn(['boat','exec',row.vm,'--timeout','20','--json','--','bun','-e',script],{stdout:'pipe',stderr:'pipe'})
  const [stdout,stderr,code]=await Promise.all([new Response(child.stdout).text(),new Response(child.stderr).text(),child.exited])
  if(code!==0)throw new Error('archive read failed '+stderr.slice(-200))
  const envelope=JSON.parse(stdout);if(envelope.exitCode!==0||envelope.stdoutTruncated)throw new Error('archive part failed')
  const part=JSON.parse(envelope.stdout);if(part.part!==i||typeof part.data!=='string')throw new Error('archive part mismatch');chunks.push(part.data)
 }
 const bytes=Buffer.from(chunks.join(''),'base64');if(createHash('sha256').update(bytes).digest('hex')!==manifest.sha256)throw new Error('archive hash mismatch')
 const dir=join(runOut,job);mkdirSync(dir,{recursive:true});writeFileSync(join(dir,'receipts.br'),bytes);writeFileSync(join(dir,'archive-manifest.json'),JSON.stringify(manifest,null,2)+'\n')
 const files=JSON.parse(brotliDecompressSync(bytes).toString()) as Record<string,string>
 for(const [name,text]of Object.entries(files)){if(name!==basename(name))throw new Error('unsafe archive name');if(['actions.jsonl','heartbeat.json'].includes(name))writeFileSync(join(dir,name),text)}
 return JSON.parse(files['result.json']!)
}
async function publish(job:string,row:any,text:string){
 let result:any,manifest:any
 for(const line of text.split('\n')){if(!line.startsWith('{'))continue;let item:any;try{item=JSON.parse(line)}catch{continue}if(item.shardResult)result=item.shardResult;if(item.artifact==='section10-chunk-manifest')manifest=item}
 if(manifest)result=await archive(job,row,manifest)
 if(!result)throw new Error('no complete result or archive manifest')
 result=normalizeSection13(result)
 delete result.trace
 const path=join(out,`${result.name}-op${result.op}.json`)
 put(path,JSON.stringify({...result,publication:{batch,job,vm:row.vm,time:new Date().toISOString(),archiveSha256:manifest?.sha256}},null,2)+'\n')
 published.add(job);console.log(JSON.stringify({published:path,verdict:result.verdict,units:result.units,wallMs:result.wallMs,archive:!!manifest}))
}
const scan=()=>{if(busy){again=true;return}busy=true
 try{
  if(!batch&&existsSync(runLog))batch=/\[boat\] batch ([^: ]+)/.exec(readFileSync(runLog,'utf8'))?.[1]
  if(!batch)return
  const rowsFile=join(queue,batch+'.rows'),placements=join(runOut,'placement.json'),rows=existsSync(rowsFile)?readFileSync(rowsFile,'utf8').trim().split('\n').flatMap(l=>{try{return [JSON.parse(l)]}catch{return []}}):existsSync(placements)?Object.entries(JSON.parse(readFileSync(placements,'utf8'))).map(([name,p]:[string,any])=>({name,vm:p.vm})):[]
  for(const job of jobs){if(published.has(job)||working.has(job)||working.size>=2)continue
   const name=job.startsWith('star-')?'Invstar-'+job.slice(5):'Inv2973-'+job.slice(8);if(existsSync(join(out,name+'.json'))){published.add(job);continue}
   const row=rows.findLast((r:any)=>r.name===job),file=join(queue,batch+'.logs',job,'out'),fallback=join(runOut,job+'.log'),source=existsSync(file)?file:fallback
   if(!row||!existsSync(source))continue
   const text=readFileSync(source,'utf8');if(!text.includes('section10-chunk-manifest')&&!text.includes('"shardResult"'))continue
   working.add(job);void publish(job,row,text).catch(e=>{console.error(JSON.stringify({publicationError:job,error:String(e)}))}).finally(()=>{working.delete(job);if(published.size===jobs.length)finish();else scan()})
  }
 }finally{busy=false;if(again){again=false;queueMicrotask(scan)}}
}
const deadline=setTimeout(()=>{for(const w of watchers)w.close();console.error(JSON.stringify({publicationIncomplete:true,published:[...published],batch}));process.exitCode=1},7200000)
watchers.push(watch(queue,{recursive:true},(_event,file)=>{if(!batch||String(file).includes(batch))scan()}))
watchers.push(watch(runLog,scan));watchers.push(watch(runOut,{recursive:true},scan));scan()
