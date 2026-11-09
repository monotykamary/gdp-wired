// Fail-closed accounting: a successful worker is not a proof.
import {readFileSync,readdirSync,writeFileSync} from 'node:fs'
const root=process.argv[2]??'runs/mldr-incl-gates-v1',errors:string[]=[]
type Kind='ic3syn'|'duoai'|'broken'
const kinds=(process.argv[3]?.split(',')??['ic3syn','duoai','broken']) as Kind[]
if(new Set(kinds).size!==kinds.length||kinds.some(k=>!['ic3syn','duoai','broken'].includes(k)))throw Error('invalid analysis scope')
type Result={verdict:string,ms:number}
type Outcome={exit?:number,result?:Result}
const proved=(o:Outcome)=>o.exit===0&&o.result?.verdict==='proven'&&o.result.ms>=0&&o.result.ms<=60000
const refuted=(o:Outcome)=>o.exit===0&&o.result?.verdict==='refuted'&&o.result.ms>=0&&o.result.ms<=60000
const suites=Object.fromEntries(kinds.map(kind=>{
 const expected=kind==='ic3syn'?87:kind==='duoai'?10:29,dir=`${root}/${kind}`,files=readdirSync(dir).filter(n=>n.endsWith('.log')).sort(),rows:{name:string,id:string,base:Outcome,cand:Outcome}[]=[]
 const receipts=new Map(readFileSync(`${dir}/summary.tsv`,'utf8').trim().split('\n').map(l=>{const [name,exit]=l.trim().split(/\s+/);return [name,Number(exit)]}))
 for(const file of files){const row={name:file.slice(0,-4),id:'',base:{} as Outcome,cand:{} as Outcome};let active:'base'|'cand'|undefined
  for(const line of readFileSync(`${dir}/${file}`,'utf8').split('\n')){
   const begin=/^PAIR begin side=(base|cand) phase=(search|broken) id=(\S+) baseline=(\S+)$/.exec(line),end=/^PAIR end side=(base|cand) phase=(search|broken) exit=(\d+)$/.exec(line)
   if(begin){active=begin[1] as 'base'|'cand';row.id=begin[3]!;if(begin[4]!=='b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c')errors.push(`${file}: wrong baseline`)}
   else if(end){const side=end[1] as 'base'|'cand';if(active!==side)errors.push(`${file}: unmatched end`);row[side].exit=Number(end[3]);active=undefined}
   else if(active&&line.startsWith('{')){let r:any;try{r=JSON.parse(line)}catch{errors.push(`${file}: invalid JSON`);continue}if(r.id===row.id){if(r.error)errors.push(`${file}/${active}: ${r.error}`);const result=r[kind==='broken'?'broken':'search'];row[active].result=result?{verdict:result.verdict,ms:result.ms}:undefined}}
  }
  if(receipts.get(row.name)!==0)errors.push(`${file}: missing/failed worker receipt`)
  for(const side of ['base','cand'] as const){const o=row[side];if(o.exit===undefined||![0,124,137].includes(o.exit)||o.exit===0&&!o.result)errors.push(`${file}/${side}: incomplete`);if(o.result&&(!Number.isFinite(o.result.ms)||o.result.ms<0))errors.push(`${file}/${side}: invalid units`)}
  rows.push(row)
 }
 if(files.length!==expected||receipts.size!==expected)errors.push(`${kind}: expected ${expected}, got ${files.length} logs/${receipts.size} receipts`)
 const lost=rows.filter(r=>proved(r.base)&&!proved(r.cand)).map(r=>r.name),gained=rows.filter(r=>!proved(r.base)&&proved(r.cand)).map(r=>r.name),falseProofs=kind==='broken'?rows.filter(r=>r.cand.result?.verdict==='proven').map(r=>r.name):[],lostRefutations=kind==='broken'?rows.filter(r=>refuted(r.base)&&!refuted(r.cand)).map(r=>r.name):[]
 return [kind,{pairs:rows.length,baseProven:rows.filter(r=>proved(r.base)).length,candidateProven:rows.filter(r=>proved(r.cand)).length,lost,gained,falseProofs,lostRefutations,rows}]
}))
const complete=kinds.length===3,componentPass=errors.length===0&&Object.values(suites).every(s=>s.lost.length===0&&s.falseProofs.length===0&&s.lostRefutations.length===0),out={complete,scope:kinds,pass:complete&&componentPass,componentPass,errors,suites}
writeFileSync(`${root}/verdicts${complete?'':'-'+kinds.join('-')}.json`,JSON.stringify(out,null,2)+'\n');console.log(JSON.stringify(out));if(!componentPass)process.exitCode=1
