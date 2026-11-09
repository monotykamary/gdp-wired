import {readFileSync,writeFileSync} from 'node:fs'
import {dirname,join} from 'node:path'
import {casesFor,SUITES,type Manifest,validatePins} from './gate-evidence.ts'
const file=process.argv[2]
if(!file)throw Error('usage: make-gates.ts MANIFEST_JSON')
const manifest=JSON.parse(readFileSync(file,'utf8')) as Manifest,errors=validatePins(manifest,{base:manifest.base.sha,cand:manifest.cand.sha});if(errors.length)throw Error(errors.join('; '))
for(const suite of SUITES){const jobs=casesFor(suite).map((c,i)=>({name:c.name,cmd:`bash research/mldr-incl/compare-main.sh ${suite} ${c.id} ${c.repeat} ${i%2?'base':'cand'} ${manifest.base.sha} ${manifest.cand.sha} ${manifest.base.archiveSha256} ${manifest.cand.archiveSha256}`,cpu:8,memory:14336,timeout:240,vm_type:'large',timing:true})),path=join(dirname(file),`${suite}-jobs.json`);writeFileSync(path,JSON.stringify(jobs,null,2)+'\n');console.log(JSON.stringify({suite,path,jobs:jobs.length}))}
