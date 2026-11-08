import {readFileSync,readdirSync,writeFileSync} from 'node:fs'
import {execFileSync} from 'node:child_process'
const dir=process.argv[2]!,files=readdirSync(dir)
const family=JSON.parse(readFileSync(`${dir}/family-first.json`,'utf8'))
console.log('FAMILY',JSON.stringify(family.laws.map((l:any)=>l.name)))
const queries=readFileSync(`${dir}/queries.jsonl`,'utf8').trim().split('\n').map(x=>JSON.parse(x))
console.log('QUERY_SUMMARY',JSON.stringify(queries.reduce((a:any,q:any)=>{const k=q.kind+':'+q.outcome;a[k]=(a[k]??0)+1;return a},{})))
const retained=files.filter(f=>f.endsWith('.json')&&!f.startsWith('stage-')).map(f=>({f,...JSON.parse(readFileSync(`${dir}/${f}`,'utf8'))})).filter(d=>d.goal&&d.outcome==='unknown').sort((a,b)=>b.ms-a.ms).slice(0,12).map(d=>d.f)
writeFileSync(`${dir}/retained.json`,JSON.stringify(retained))
const data=execFileSync('tar',['-C',dir,'-cJf','-','family.json','family-first.json','queries.jsonl','retained.json',...retained])
console.log('ARCHIVE_BASE64',data.toString('base64'))
