import {readFileSync,writeFileSync} from 'node:fs'
import {brotliDecompressSync} from 'node:zlib'
import {createHash} from 'node:crypto'
const root=process.argv[2]??'runs/mldr-incl-step-v1',archive=JSON.parse(brotliDecompressSync(readFileSync('research/mldr-incl/fixtures/safety-gp1.br')).toString()),jobs=JSON.parse(readFileSync('research/mldr-incl/replay-jobs.json','utf8')) as {name:string}[],errors:string[]=[],rows:any[]=[]
const receipts=new Map(readFileSync(`${root}/summary.tsv`,'utf8').trim().split('\n').map(l=>{const [name,exit]=l.trim().split(/\s+/);return [name,Number(exit)]}))
for(const {name} of jobs){const file=`${root}/${name}.log`;let lines:string[];try{lines=readFileSync(file,'utf8').split('\n')}catch{errors.push(`${name}: missing log`);continue}if(receipts.get(name)!==0)errors.push(`${name}: missing/failed receipt`)
 const results=lines.filter(l=>l.startsWith('{')).map(l=>{try{return JSON.parse(l)}catch{return {}}}).filter(r=>typeof r.mode==='string'&&typeof r.proven==='boolean')
 if(results.length!==1){errors.push(`${name}: expected one result`);continue}const row=results[0],stage=/^(stage-\d+)-/.exec(name)?.[1],text=archive[`${stage}.json`]
 if(typeof text!=='string'||row.inputSha256!==createHash('sha256').update(text).digest('hex'))errors.push(`${name}: frozen-input hash mismatch`)
 if(row.proven&&!row.checked)errors.push(`${name}: unchecked proof`)
 rows.push({name,...row})
}
if(receipts.size!==jobs.length)errors.push(`expected ${jobs.length} receipts, got ${receipts.size}`)
const groups=Object.fromEntries(['raw','preferred','keyed','seeded'].map(mode=>{const rs=rows.filter(r=>r.mode===mode);return [mode,{count:rs.length,checked:rs.filter(r=>r.proven&&r.checked).length,sat:rs.filter(r=>r.stuck==='sat').length,unknown:rs.filter(r=>!r.proven&&r.stuck!=='sat').length,inclusionPackets:rs.filter(r=>r.poolAdded>0).length,preferredPackets:rs.filter(r=>r.preferred>0).length}]})),out={complete:errors.length===0,errors,groups,rows}
writeFileSync(`${root}/analysis.json`,JSON.stringify(out,null,2)+'\n');console.log(JSON.stringify({complete:out.complete,errors,groups}));if(errors.length)process.exitCode=1
