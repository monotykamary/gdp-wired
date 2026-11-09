import {readFileSync,readdirSync,writeFileSync} from 'node:fs'
import {brotliDecompressSync} from 'node:zlib'
import {createHash} from 'node:crypto'
const root=process.argv[2]??'runs/mldr-incl-step-v1',fixture=process.argv[3]??'research/mldr-incl/fixtures/safety-gp1.br',plan=process.argv[4]??'research/mldr-incl/replay-jobs.json',archive=JSON.parse(brotliDecompressSync(readFileSync(fixture)).toString()),jobs=JSON.parse(readFileSync(plan,'utf8')) as {name:string}[],errors:string[]=[],rows:any[]=[],names=new Set(jobs.map(j=>j.name))
if(names.size!==jobs.length)errors.push('duplicate planned job name')
const receiptLines=readFileSync(`${root}/summary.tsv`,'utf8').trim().split('\n').filter(Boolean),receipts=new Map<string,number>()
for(const line of receiptLines){const [name,exit]=line.trim().split(/\s+/);if(!name||!names.has(name)||receipts.has(name))errors.push('duplicate or unexpected receipt');if(name)receipts.set(name,Number(exit))}
for(const file of readdirSync(root).filter(f=>f.endsWith('.log')))if(!names.has(file.slice(0,-4)))errors.push(`unexpected log ${file}`)
for(const {name} of jobs){const match=/^(stage-\d+)-(raw|preferred|keyed|seeded)-(250|1000|2700)$/.exec(name);if(!match){errors.push(`${name}: malformed case identity`);continue}const file=`${root}/${name}.log`;let lines:string[];try{lines=readFileSync(file,'utf8').split('\n')}catch{errors.push(`${name}: missing log`);continue}if(receipts.get(name)!==0)errors.push(`${name}: missing/failed receipt`)
 const results=lines.filter(l=>l.startsWith('{')).map(l=>{try{return JSON.parse(l)}catch{return {}}}).filter(r=>typeof r.mode==='string'&&typeof r.proven==='boolean')
 if(results.length!==1){errors.push(`${name}: expected one result`);continue}const row=results[0],text=archive[`${match[1]}.json`]
 if(row.mode!==match[2]||row.ms!==Number(match[3]))errors.push(`${name}: mode/budget identity mismatch`)
 if(typeof text!=='string'||row.inputSha256!==createHash('sha256').update(text).digest('hex'))errors.push(`${name}: frozen-input hash mismatch`)
 if(typeof row.checked!=='boolean'||row.proven&&!row.checked)errors.push(`${name}: unchecked proof`)
 rows.push({name,...row})
}
if(receiptLines.length!==jobs.length||receipts.size!==jobs.length)errors.push(`expected ${jobs.length} distinct receipts, got ${receiptLines.length} rows/${receipts.size} names`)
const groups=Object.fromEntries(['raw','preferred','keyed','seeded'].map(mode=>{const rs=rows.filter(r=>r.mode===mode);return [mode,{count:rs.length,checked:rs.filter(r=>r.proven&&r.checked).length,sat:rs.filter(r=>r.stuck==='sat').length,unknown:rs.filter(r=>!r.proven&&r.stuck!=='sat').length,inclusionPackets:rs.filter(r=>r.poolAdded>0).length,preferredPackets:rs.filter(r=>r.preferred>0).length}]})),out={complete:errors.length===0,fixture,plan,errors,groups,rows}
writeFileSync(`${root}/analysis.json`,JSON.stringify(out,null,2)+'\n');console.log(JSON.stringify({...out,rows:undefined}));if(errors.length)process.exitCode=1
