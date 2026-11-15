// Small symbolic sharded put-only model. The candidates below are selected by
// index from the sealed retained family, never authored as helper formulas.
import {writeFileSync} from 'node:fs'
import type {Machine,E} from '../../core/machine.ts'
import {proveSetFast, withDeadline, clock} from '../../kernel/prove.ts'
import {proveCandidateSeeds} from '../../core/candidate-seeds.ts'
import {loadCandidateSeedManifest} from './candidate-seed-manifest.ts'
const v=(name:string):E=>({op:'var',name}), n=(value:number):E=>({op:'const',value})
const tuple=(a:E,b:E):E=>({op:'tup',a,b})
const at=(map:string,key:E):E=>({op:'get',map,key})
const m:Machine={name:'symbolic sharded put',params:['nodes','keys'],inputs:['node','key'],state:{},maps:{Table:0,Owner:0},relations:{Table:['Node','Key'],Owner:['Key','Node']},
 assume:{op:'and',xs:[{op:'<',a:v('node'),b:v('nodes')},{op:'<',a:v('key'),b:v('keys')}]},
 step:{maps:{Table:{key:tuple(v('node'),v('key')),value:{op:'if',c:{op:'<=',a:n(1),b:at('Owner',tuple(v('key'),v('node')))},then:n(1),else:at('Table',tuple(v('node'),v('key')))}}}}}
const load=loadCandidateSeedManifest('research/bapa/candidate-seed-sharded.manifest.json',m)
const item=(i:number)=>{const a=load.audit.laws[i];if(!a||a.status!=='candidate')throw Error(`retained law ${i} not translated: ${JSON.stringify(a)}`);return a.law}
const publicLaw={...item(4),name:'one table owner per key'}
const candidates=[item(5),item(10),item(19)]
const result=withDeadline(clock()+180000,()=>{
 const unseeded=proveSetFast(m,[publicLaw])
 const seeded=proveCandidateSeeds(m,[publicLaw],candidates)
 return {unseeded,seeded}
})
const audit={manifest:load.audit,unseeded:{proven:result.unseeded.proven,checked:result.unseeded.checked,failed:result.unseeded.failed},seeded:result.seeded.status==='checked'?{status:result.seeded.status,kept:result.seeded.kept.map(x=>x.name),dropped:result.seeded.dropped,proven:result.seeded.closure.proven,checked:result.seeded.closure.checked}:{...result.seeded,kept:result.seeded.kept.map(x=>x.name)}}
writeFileSync(`${process.env.SUPERCOMPUTER_OUTPUT_DIR}/candidate-seed-symbolic.json`,JSON.stringify(audit,null,2)+'\n')
if(result.unseeded.proven&&result.unseeded.checked)throw Error('unseeded model unexpectedly inductive')
if(result.seeded.status!=='checked')throw Error('seeded full family not checked')
if(!result.seeded.kept.length)throw Error('no mechanically seeded law retained')
console.log(JSON.stringify({unseeded:audit.unseeded,seeded:audit.seeded}))
