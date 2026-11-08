// Read-only verdict accounting followed by a small report; never equate a job exit with a proof.
import {existsSync,readFileSync,readdirSync,writeFileSync} from 'node:fs'
const root=process.argv[2]??'runs/track-p-gates',shardDir=process.argv[3]??root+'/shard',brokenRetry=process.argv[4]??root+'/broken-retry'
type Row={id:string,error?:string,search?:{verdict:string,ms:number},broken?:{verdict:string,ms:number}}
type Outcome={exit?:number,row?:Row}
type Pair={name:string,id:string,run:number,cand:Outcome,base:Outcome}
const errors:string[]=[]
const lines=(file:string)=>readFileSync(file,'utf8').split('\n')
const logs=(dir:string)=>readdirSync(dir).filter(n=>n.endsWith('.log')).sort()
const proven=(o:Outcome)=>o.exit===0&&o.row?.search?.verdict==='proven'&&o.row.search.ms<=60000
function paired(suite:string,expected:number){
 const dir=root+'/'+suite,rows:Pair[]=[]
 for(const name of logs(dir)){
  const p:Pair={name,id:'',run:0,cand:{},base:{} };let side:'cand'|'base'|undefined
  for(const line of lines(dir+'/'+name)){
   const begin=/^PAIR begin side=(cand|base) id=(\S+) run=(\d+)/.exec(line),end=/^PAIR end side=(cand|base) exit=(\d+)/.exec(line)
   if(begin){side=begin[1] as 'cand'|'base';p.id=begin[2]!;p.run=Number(begin[3])}
   else if(end){p[end[1] as 'cand'|'base'].exit=Number(end[2]);side=undefined}
   else if(side&&line.startsWith('{')){const row=JSON.parse(line) as Row;if(row.id)p[side].row=row}
  }
  for(const s of ['cand','base']as const){const o=p[s];if(o.exit===undefined||![0,124,137].includes(o.exit)||o.row?.error||o.exit===0&&!o.row?.search)errors.push(`${suite}/${name}/${s}: incomplete or error`)}
  rows.push(p)
 }
 if(rows.length!==expected)errors.push(`${suite}: expected ${expected} pairs, got ${rows.length}`)
 const regressions=rows.filter(p=>proven(p.base)&&!proven(p.cand)),gains=rows.filter(p=>!proven(p.base)&&proven(p.cand))
 const protocols=[...new Set(rows.map(r=>r.id))].sort().map(id=>{const ps=rows.filter(r=>r.id===id);return {id,runs:ps.length,cand:ps.filter(p=>proven(p.cand)).length,base:ps.filter(p=>proven(p.base)).length}})
 return {pairs:rows.length,cand:rows.filter(p=>proven(p.cand)).length,base:rows.filter(p=>proven(p.base)).length,regressions:regressions.map(p=>p.name),gains:gains.map(p=>p.name),protocols}
}
const ic3syn=paired('ic3syn-paired',87)
if(process.argv.includes('--ic3syn')){console.log(JSON.stringify({errors,ic3syn}));process.exit(errors.length||ic3syn.regressions.length?1:0)}
const duoai=paired('duoai-paired',10)
if(process.argv.includes('--pairs')){console.log(JSON.stringify({errors,ic3syn,duoai}));process.exit(errors.length||ic3syn.regressions.length||duoai.regressions.length?1:0)}
const broken={total:0,proven:[] as string[],refuted:0,unknown:0,timeouts:0}
for(const name of logs(root+'/broken')){
 broken.total++;const ls=lines(existsSync(brokenRetry+'/'+name)?brokenRetry+'/'+name:root+'/broken/'+name),row=ls.filter(l=>l.startsWith('{')).map(l=>JSON.parse(l) as Row).find(r=>r.id),exit=Number(ls.find(l=>l.startsWith('BROKEN_EXIT='))?.slice(12))
 if(row?.error||!Number.isFinite(exit)||![0,124,137].includes(exit)||exit===0&&!row?.broken)errors.push('broken/'+name+': incomplete or error')
 if(row?.broken?.verdict==='proven')broken.proven.push(name)
 else if(row?.broken?.verdict==='refuted')broken.refuted++
 else if(exit===124||exit===137)broken.timeouts++
 else broken.unknown++
}
if(broken.total!==29)errors.push(`broken: expected 29, got ${broken.total}`)
const shardRows=lines(shardDir+'/summary.tsv').filter(l=>/^shard-\d+\s/.test(l)).map(l=>{const [name,exit,seconds]=l.split(/\s+/);return {name:name!,exit:Number(exit),seconds:Number(seconds)}})
if(shardRows.length!==7||shardRows.some(r=>r.exit!==0))errors.push('shards: incomplete or failing')
const passes=logs(shardDir).reduce((n,f)=>n+[...readFileSync(shardDir+'/'+f,'utf8').matchAll(/^\s*(\d+) pass\s*$/gm)].reduce((s,m)=>s+Number(m[1]),0),0)
const out={checked:new Date().toISOString(),passes:!errors.length&&!ic3syn.regressions.length&&!duoai.regressions.length&&!broken.proven.length,errors,ic3syn,duoai,broken,shards:{directory:shardDir,rows:shardRows,tests:passes}}
writeFileSync(root+'/summary.json',JSON.stringify(out,null,2)+'\n')
const md=['# Track P gate verdicts','',`- IC3Syn: candidate ${ic3syn.cand}/${ic3syn.pairs}, base ${ic3syn.base}/${ic3syn.pairs}; pair losses ${ic3syn.regressions.length}.`,`- DuoAI: candidate ${duoai.cand}/${duoai.pairs}, base ${duoai.base}/${duoai.pairs}; pair losses ${duoai.regressions.length}.`,`- Broken: ${broken.proven.length} proven; ${broken.refuted} refuted, ${broken.unknown} unknown, ${broken.timeouts} strict timeouts.`,`- Shards: ${shardRows.filter(r=>r.exit===0).length}/7 passed; ${passes} Bun tests.`,`- Errors: ${errors.length}.`,'','| Suite | Protocol | Candidate | Base |','| --- | --- | ---: | ---: |',...([['IC3Syn',ic3syn],['DuoAI',duoai]]as const).flatMap(([suite,data])=>data.protocols.map(p=>`| ${suite} | ${p.id} | ${p.cand}/${p.runs} | ${p.base}/${p.runs} |`))]
writeFileSync(root+'/SUMMARY.md',md.join('\n')+'\n')
console.log(JSON.stringify(out))
if(!out.passes)process.exitCode=1
