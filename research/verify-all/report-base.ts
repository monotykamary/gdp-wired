// Tables from original-harness logs. Run on boat; raw found laws remain verbatim in hash-addressed logs.
import {readFileSync,readdirSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {join} from 'node:path'
const root=process.argv[2]??'evidence', dir=join(root,'production')
const hash=(s:string)=>createHash('sha256').update(s).digest('hex')
const rows=readdirSync(dir).filter(f=>f.endsWith('.log')).map(file=>{const text=readFileSync(join(dir,file),'utf8'), meta=text.match(/VERIFY suite=(\S+) id=(\S+) repeat=(\d+) mode=(\S+)/)!,output=text.split('\n').flatMap(l=>{try{return[JSON.parse(l)]}catch{return[]}}).find(o=>o.id);return{file,suite:meta[1]!,id:meta[2]!,repeat:+meta[3]!,mode:meta[4]!,output,wall:text.match(/WALL seconds=([0-9.]+)/)?.[1],exit:+(text.match(/RESULT exit=(\d+)/)?.[1]??-1),sha256:hash(text)}})
const brief=(r:any)=>{if(!r)return'—';const v=r.output?.[r.mode==='search'?'search':'broken'];return`${v?.verdict??'timeout'}/${r.wall??'—'} s/${v?.ms??'—'} ms/${v?.work??'—'}/${v?.full??'—'}/F${v?.found?.length??0}`}
console.log('## 1. Production reruns\n\nEach cell is `verdict / strict wall s / harness ms / work / full / found-law count`. `work` and `full` are the original IC3Syn counters, not wall seconds. Full found-law text and the kernel hash are in every linked log. `F` is not a count of individually proven laws: notably an unknown counted search can print its candidate family.\n')
console.log('| IC3Syn protocol | Repeat 1 | Repeat 2 | Repeat 3 | Broken (one run) |')
console.log('|---|---|---|---|---|')
for(const id of [...new Set(rows.filter(r=>r.suite==='ic3syn').map(r=>r.id))].sort()){
 const get=(mode:string,n:number)=>rows.find(r=>r.suite==='ic3syn'&&r.id===id&&r.mode===mode&&r.repeat===n)
 const link=(r:any)=>r?`[${brief(r)}](verify-all/production/${r.file})`:'—'
 console.log(`| ${id} | ${[1,2,3].map(n=>link(get('search',n))).join(' | ')} | ${link(get('broken',1))} |`)
}
console.log('\n### DuoAI controls\n\nThe unpaired original harness does not emit counted work; no work counter was invented. Paired archived-baseline/current results are additional evidence, not part of the IC3Syn numerator.\n')
console.log('| DuoAI protocol | Repeat 1 | Repeat 2 | Repeat 3 | Paired base/candidate |\n|---|---|---|---|---|')
for(const id of [...new Set(rows.filter(r=>r.suite==='duoai').map(r=>r.id))].sort()){
 const links=[1,2,3].map(n=>{const r=rows.find(r=>r.suite==='duoai'&&r.id===id&&r.repeat===n)!;return`[${brief(r)}](verify-all/production/${r.file})`})
 let pairs:string[]=[]
 for(const n of[1,2,3]){const p=join(root,'duo-paired',`paired-${id}-r${n}.log`),t=readFileSync(p,'utf8');const vals=[...t.matchAll(/PAIR begin side=(\w+) id=\S+ run=\d+\n([\s\S]*?)PAIR end side=\1 exit=(\d+)/g)].map(m=>{const o=m[2]!.split('\n').flatMap(l=>{try{return[JSON.parse(l)]}catch{return[]}}).find(x=>x.id);return`${m[1]}:${o?.search?.verdict??'missing'}(${o?.search?.ms??'—'} ms, exit ${m[3]})`});pairs.push(`[r${n} ${vals.join(', ')}](verify-all/duo-paired/paired-${id}-r${n}.log)`)}
 console.log(`| ${id} | ${links.join(' | ')} | ${pairs.join('<br>')} |`)
}
console.log('\n### Original-run evidence hashes\n\nFull SHA-256 per log (includes stdout, wall, affinity, and in-job kernel identity):\n\n```text')
for(const r of rows.sort((a,b)=>a.file.localeCompare(b.file)))console.log(`${r.sha256}  verify-all/production/${r.file}`)
console.log('```')
