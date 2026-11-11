import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
const input=process.argv[2];assert(input)
const summary=readFileSync(join(input,'summary.tsv'),'utf8').trim().split('\n').map(line=>line.split('\t'))
const eprOnly=process.argv[3]==='epr-only',work=Number(process.argv[4]??15000000)
const reports:any[]=[]
const groups:[string,string,string][]=eprOnly?[['epr-original','consensus_epr','1']]:[['ordinary-original','consensus','0'],['epr-original','consensus_epr','1']]
for(const [prefix,id,exit]of groups){
 const runs:any[][]=[1,2].map((rep:number):any[]=>{
  const name=prefix+'-'+rep;assert(summary.some(([job,code])=>job===name&&code===exit))
  const text:string=readFileSync(join(input,name+'.log'),'utf8'),rows:any[]=text.split('\n').filter(line=>line.startsWith('ORIGINAL_PATH_CASE ')).map(line=>JSON.parse(line.slice('ORIGINAL_PATH_CASE '.length)))
  assert.equal(rows.length,2)
  for(const [index,row]of rows.entries()){assert.equal(row.id,id);assert.equal(row.repetition,rep);assert.equal(row.variant,index===0?'original':'broken');assert.equal(row.source,'cd00524f01093838e9584edc4a20f71e2be10e2a');assert.equal(row.work,work);assert(row.audit.exclusiveReconciled);if(index===1)assert.notEqual(row.result.verdict,'proven')}
  if(exit==='1')assert(text.includes('requested production path was not observed'))
  return rows
 })
 const stable=(rows:any[])=>rows.map(({variant,raw,result,audit,weights})=>({variant,raw,result,audit,weights}))
 assert.deepEqual(stable(runs[0]!),stable(runs[1]!))
 const original=runs[0]![0];assert(original)
 if(exit==='0')assert(original.raw.fm>0||original.raw.plainRows>0);else assert.equal(original.raw.epr,0)
 reports.push({id,expectedExit:exit,deterministic:true,raw:original.raw,result:original.result})
}
console.log('ORIGINAL_PATH_AUDIT '+JSON.stringify({passed:true,ordinaryCoverage:!eprOnly,eprCoverage:false,reports,scope:'explicit diagnostic weights; EPR failure retained, no W or all-29 qualification'}))
