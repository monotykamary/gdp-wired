// Parse full receipts, not scheduler success. A timeout is never a proof.
import {readFileSync,readdirSync,writeFileSync} from 'node:fs'
const root=process.argv[2]??'runs/track-gen-gates-v2',errors:string[]=[]
type Result={exit?:number,row?:{id:string,error?:string,search?:{verdict:string,ms:number},broken?:{verdict:string}}}
const logs=(path:string)=>readdirSync(path).filter(p=>p.endsWith('.log')).sort()
const lines=(path:string)=>readFileSync(path,'utf8').split('\n')
const proved=(r:Result)=>r.exit===0&&r.row?.search?.verdict==='proven'&&r.row.search.ms<=60000
function pairs(suite:string,expected:number){
 const rows:{file:string,id:string,run:number,cand:Result,base:Result}[]=[]
 for(const file of logs(`${root}/${suite}`)){
  const record={file,id:'',run:0,cand:{} as Result,base:{} as Result};let side:'cand'|'base'|undefined
  for(const line of lines(`${root}/${suite}/${file}`)){
   const begin=/^PAIR begin side=(cand|base) id=(\S+) run=(\d+)/.exec(line),end=/^PAIR end side=(cand|base) exit=(\d+)/.exec(line)
   if(begin){side=begin[1] as 'cand'|'base';record.id=begin[2]!;record.run=Number(begin[3])}
   else if(end){record[end[1] as 'cand'|'base'].exit=Number(end[2]);side=undefined}
   else if(side&&line.startsWith('{"id"'))record[side].row=JSON.parse(line)
  }
  for(const s of ['base','cand'] as const){const r=record[s];if(![0,124,137].includes(r.exit??-1)||r.row?.error||r.exit===0&&!r.row?.search)errors.push(`${suite}/${file}/${s}: incomplete or error`)}
  rows.push(record)
 }
 if(rows.length!==expected||new Set(rows.map(r=>`${r.id}:${r.run}`)).size!==expected)errors.push(`${suite}: expected ${expected} unique pairs`)
 return {pairs:rows.length,candidate:rows.filter(r=>proved(r.cand)).length,baseline:rows.filter(r=>proved(r.base)).length,losses:rows.filter(r=>proved(r.base)&&!proved(r.cand)).map(r=>r.file),gains:rows.filter(r=>!proved(r.base)&&proved(r.cand)).map(r=>r.file),rows}
}
const ic3syn=pairs('ic3syn',87),duoai=pairs('duoai',10)
const broken={total:0,proven:[] as string[],refuted:0,unknown:0,timeouts:0}
for(const file of logs(`${root}/broken`)){
 const ls=lines(`${root}/broken/${file}`),row=ls.filter(l=>l.startsWith('{"id"')).map(l=>JSON.parse(l)).at(-1),exit=Number(ls.find(l=>l.startsWith('BROKEN_EXIT='))?.slice(12))
 broken.total++
 if(![0,124,137].includes(exit)||row?.error||exit===0&&!row?.broken)errors.push(`broken/${file}: incomplete or error`)
 if(row?.broken?.verdict==='proven')broken.proven.push(file)
 else if(row?.broken?.verdict==='refuted')broken.refuted++
 else if(exit===124||exit===137)broken.timeouts++
 else broken.unknown++
}
if(broken.total!==29)errors.push(`broken: expected 29, got ${broken.total}`)
const passed=!errors.length&&!ic3syn.losses.length&&!duoai.losses.length&&!broken.proven.length
const result={passed,baseline:'6a3874d3',errors,ic3syn,duoai,broken}
writeFileSync(`${root}/verified.json`,JSON.stringify(result,null,2)+'\n')
console.log(JSON.stringify({...result,ic3syn:{...ic3syn,rows:undefined},duoai:{...duoai,rows:undefined}}))
if(!passed)process.exitCode=1
