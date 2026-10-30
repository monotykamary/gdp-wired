import {readFileSync,writeFileSync,appendFileSync} from 'node:fs'
import {extractPython} from '../../../core/extract-py.ts'
import {extractRuby} from '../../../core/extract-rb.ts'
import {extractJava} from '../../../core/extract-jvm.ts'
import {extract} from '../../../core/extract.ts'
import {proveRule} from '../../../core/dsl.ts'
const dir=import.meta.dir, cases=JSON.parse(readFileSync(`${dir}/cases.json`,'utf8')), c=cases.find((x:any)=>x.id===process.argv[2]); if(!c) throw Error('unknown case')
const check={runs:30,depth:6,states:60}, file=`${dir}/${c.file}`
let result:any={case:c.id};
try {
 const opts:any={entry:c.discover?undefined:'Meter',check}; let x:any
 if(c.lang==='Python') x=extractPython(file,opts)
 else if(c.lang==='Ruby') x=extractRuby(file,{...opts,root:dir})
 else if(c.lang==='Java') x=extractJava(file,{...opts,root:`${dir}/${c.id}`})
 else x=extract(readFileSync(file,'utf8'),{...opts,file:'case.ts'})
 result.ok=x.ok; result.refusals=x.refusals; result.notes=x.notes; result.evidence=x.evidence; result.source=x.source;
 if(x.ok){ try {const r=x.rule; const v=proveRule(r,[...(x.invariants??[]),r.law('n stays zero',({n}:any)=>n.eq(0))],{search:false}); result.proof={proven:v.proven,checked:v.checked,stuck:v.stuck,goal:v.goal,witness:v.witness,run:v.run};}catch(e){result.proofError=String(e)} }
} catch(e){result.exception=String(e)}
writeFileSync(`${dir}/${c.id}.json`,JSON.stringify(result,null,2))
let actual:string,verdict:string
if(result.exception){actual=`error: ${result.exception}`;verdict='UNSURE'}
else if(!result.ok){actual=`refused: ${(result.refusals??[]).map((r:any)=>r.what).join('; ')}`;verdict='OK'}
else if(result.proofError){actual=`accepted; law error: ${result.proofError}`;verdict='UNSURE'}
else {const p=result.proof;actual=p.proven&&p.checked?'proven and checked':p.proven?'proven, not checked':`not proven (${p.stuck??'no status'})`;verdict=(p.proven&&p.checked)?'UNSURE':(p.stuck==='sat'?'OK':'UNSURE')}
const cell=(s:any)=>String(s).replaceAll('|','\\|').replaceAll('\n',' ').slice(0,400)
appendFileSync(`${dir}/RESULTS.md`,`| [${c.id}](${c.file}) | ${c.lang} | ${cell(c.attack)} | ${c.pred} | ${cell(actual)} | ${verdict} |\n`)
console.log(`${c.id}: ${actual} — ${verdict}`)
