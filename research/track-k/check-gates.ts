// Verify completed boat receipts. No proof search or acceptance of a missing result.
import assert from 'node:assert/strict'
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
const [kind,dir] = process.argv.slice(2) as [string,string]
const jobs=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(l=>{const [name,exit,seconds,where]=l.split('\t');assert.equal(Number(exit),0,`${name}: runner failed`);assert.equal(where,'boat',`${name}: not boat`);return {name:name!,seconds:Number(seconds)}})
const jsonLines=(text:string):any[]=>text.split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l))
let result:object
if(kind==='paired'){
 const rows=jobs.map(job=>{
  let side='',id='',run=0;const found:Record<string,any>={},exits:Record<string,number>={}
  for(const line of readFileSync(join(dir,job.name+'.log'),'utf8').split('\n')){
   const begin=/^PAIR begin side=(base|cand) id=(\S+) run=(\d+)$/.exec(line)
   if(begin){side=begin[1]!;id=begin[2]!;run=Number(begin[3]);continue}
   const end=/^PAIR end side=(base|cand) exit=(\d+)$/.exec(line)
   if(end)exits[end[1]!]=Number(end[2])
   if(line.startsWith('{')){const row=JSON.parse(line);if(row.id===id)found[side]=row}
  }
  for(const s of ['base','cand'])if(!found[s]){
   assert([124,137].includes(exits[s]!),`${job.name}: missing ${s} result without timeout receipt`)
   found[s]={search:{verdict:'unknown'},timeout:exits[s]}
  }
  assert(id&&run&&found.base&&found.cand,`${job.name}: missing paired result`)
  assert(!found.base.error&&!found.cand.error,`${job.name}: protocol error`)
  const base=found.base.search?.verdict==='proven',cand=found.cand.search?.verdict==='proven'
  assert(!base||cand,`${job.name}: lost a main proof`)
  return {id,run,base,cand}
 })
 assert([87,10].includes(rows.length),'incomplete paired suite')
 const repeats=[...new Set(rows.map(r=>r.run))].sort((a,b)=>a-b).map(run=>({run,base:rows.filter(r=>r.run===run&&r.base).length,candidate:rows.filter(r=>r.run===run&&r.cand).length}))
 const paxos=rows.filter(r=>r.id==='paxos_epr');assert(paxos.every(r=>r.cand),'paxos loss')
 result={kind,jobs:jobs.length,repeats,lost:0,paxos:paxos.map(r=>r.cand),rows}
}else if(kind==='broken'){
 const rows=jobs.flatMap(job=>jsonLines(readFileSync(join(dir,job.name+'.log'),'utf8')).filter(r=>r.id))
 assert.equal(rows.length,29);assert.equal(new Set(rows.map(r=>r.id)).size,29)
 for(const r of rows){assert(!r.error,`${r.id}: error`);assert(r.broken,`${r.id}: missing broken variant`);assert.notEqual(r.broken.verdict,'proven',r.id)}
 result={kind,jobs:jobs.length,proven:0,refuted:rows.filter(r=>r.broken.verdict==='refuted').length,unknown:rows.filter(r=>r.broken.verdict==='unknown').length}
}else if(kind==='paxos'){
 const rows=jobs.map(job=>{const r=jsonLines(readFileSync(join(dir,job.name+'.log'),'utf8')).find(r=>r.id==='paxos_epr');assert(r&&!r.error);assert.equal(r.search.verdict,'proven');assert(r.search.ms<=60000);return {name:job.name,ms:r.search.ms}})
 result={kind,rows}
}else if(kind==='shards'){
 assert.equal(jobs.length,7);result={kind,jobs:jobs.length,passed:true}
}else throw Error(`Unknown gate kind ${kind}`)
writeFileSync(join(dir,'verified.json'),JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify(result,null,2))
