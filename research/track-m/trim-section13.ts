// Streaming file edit: remove the top-level columns array from our own pretty
// JSON format without parsing or allocating its potentially multi-GB contents.
import {createReadStream} from 'node:fs'
import {open,rename,stat,readdir} from 'node:fs/promises'
import {join} from 'node:path'
const directory=process.argv[2];if(!directory)throw new Error('directory required')
const start=Buffer.from('\n  "columns": ['),ends=[Buffer.from('\n  "packetScope":'),Buffer.from('\n  "publication":')]
for(const name of await readdir(directory)){
 if(!/^Inv(?:star|2973)-op\d+\.json$/.test(name))continue
 const path=join(directory,name),temp=path+'.trim',before=(await stat(path)).size,file=await open(temp,'w')
 let mode:'before'|'skip'|'after'='before',tail=Buffer.alloc(0),found=false
 try{
  for await(const chunk of createReadStream(path,{highWaterMark:1024*1024})){
   let data=Buffer.concat([tail,chunk as Buffer]);tail=Buffer.alloc(0)
   if(mode==='before'){
    const at=data.indexOf(start)
    if(at<0){const cut=Math.max(0,data.length-64);await file.write(data.subarray(0,cut));tail=data.subarray(cut);continue}
    await file.write(data.subarray(0,at));data=data.subarray(at+start.length);mode='skip';found=true
   }
   if(mode==='skip'){
    const at=ends.map(e=>data.indexOf(e)).filter(i=>i>=0).sort((a,b)=>a-b)[0]
    if(at===undefined){tail=data.subarray(Math.max(0,data.length-64));continue}
    mode='after';data=data.subarray(at)
   }
   await file.write(data)
  }
  if(mode==='skip')throw new Error('unterminated top-level columns: '+name)
  if(tail.length)await file.write(tail)
 }finally{await file.close()}
 await rename(temp,path)
 console.log(JSON.stringify({file:path,columnsRemoved:found,before,after:(await stat(path)).size}))
}
