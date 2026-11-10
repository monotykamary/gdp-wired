import {readFileSync,writeFileSync,existsSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
import {auditT9A,packetHash} from './section9-ta-audit.ts'
const [log,dir,reference]=process.argv.slice(2);if(!log||!dir)throw new Error('LOG DIR [REFERENCE] required')
for(const line of readFileSync(log,'utf8').split('\n')){if(!line.startsWith('{'))continue;const r=JSON.parse(line);if(r.encoding==='gzip-base64'&&/^(?:[AB][1-3]\.(?:json|stderr\.log|capture\.log)|summary\.json)$/.test(r.artifact))writeFileSync(join(dir,r.artifact),gunzipSync(Buffer.from(r.data,'base64')))}
const files=['A1','B1','A2','B2','A3','B3'].map(id=>join(dir,id+'.json'))
if(files.some(f=>!existsSync(f)))throw new Error('incomplete results')
const records=files.map(f=>JSON.parse(readFileSync(f,'utf8'))),prior=reference?JSON.parse(readFileSync(reference,'utf8')):undefined,hash=prior?packetHash(prior.g,prior.cert,prior.path):undefined
const audit=auditT9A(records,hash);writeFileSync(join(dir,'audit.json'),JSON.stringify(audit,null,2)+'\n')
const gap=records.find(r=>r.side==='B'&&r.generatorGap)
if(gap){const branch=gap.branches.find((b:any)=>b.name==='complement');writeFileSync(join(dir,'generator-gap.json'),JSON.stringify({law:gap.law,packetHash:gap.packetHash,branch:'a$# = i; j$ < i; CT[i] < CfgT[j$]',protocolCounterexample:false,path:branch.path,numeric:branch.queries.at(-1),sources:branch.attempts},null,2)+'\n')}
console.log(JSON.stringify({...audit,branches:records.filter(r=>r.side==='B').map(r=>({repeat:r.repeat,generated:r.generated,branches:r.branches.map((b:any)=>({name:b.name,outcome:b.outcome,reason:b.reason,units:b.countedUnits,models:b.queries.map((q:any)=>({outcome:q.outcome,valid:q.validModel,V:q.violated})),attempts:b.attempts.map((a:any)=>({index:a.originalIndex,outcome:a.outcome,core:a.coreSize,units:a.countedUnits,valid:a.sourceAndScopeValid}))}))}))},null,2))
