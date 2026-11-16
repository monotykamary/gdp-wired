// A new symbolic-size, no-given-helper fixture. One native search; subsequent
// emission runs in another process and consumes this exact saved closure.
import {createHash} from 'node:crypto'
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {installProfile,profile049,defaultWork} from './proof-worker.ts'
installProfile(process.env)
const [{rule,nat,bool,sizedSort,everyKey,forall,when,yes},{proveRule},{captureFinalInvocation}]=await Promise.all([
 import('../../core/dsl.ts'),import('../../core/dsl.ts'),import('./proof-capture-native.ts')])
const r=rule('symbolic sized choice').params({size:nat}).sorts('Node')
 .inputs({v:nat}).assume(({size,v})=>sizedSort('Node',size).has(v))
 .maps({Chosen:bool.from(false)})
 .flags(({Chosen})=>({none:everyKey(k=>Chosen.at(k).not())}))
 .step(({Chosen,v,none})=>({Chosen:Chosen.set(v,when(none,yes,Chosen.at(v)))}))
const laws=[r.law('at most one symbolic node chosen',({Chosen})=>forall((a,b)=>Chosen.at(a).and(Chosen.at(b)).implies(a.eq(b))))]
const out=join(process.env.SUPERCOMPUTER_OUTPUT_DIR!,'symbolic-capture');mkdirSync(out)
const hash=(s:string|Uint8Array)=>createHash('sha256').update(s).digest('hex')
const result=captureFinalInvocation(join(out,'closure'),{protocol:'symbolic_choice',invocation:'export-smoke-one',
 sourceCommit:process.env.BAPA_SOURCE_COMMIT!,sourceTree:process.env.BAPA_SOURCE_TREE!,driverSha256:hash(readFileSync(new URL(import.meta.url))),
 inputSha256:hash(readFileSync(new URL(import.meta.url))),runtimeSha256:hash(readFileSync(process.execPath)),profileSha256:hash(readFileSync(new URL('./profile-049.json',import.meta.url))),
 workBudget:String(defaultWork('consensus')),flags:{...profile049}}, {laws},()=>proveRule(r,laws,{search:{work:defaultWork('consensus')}}))
writeFileSync(join(out,'native-result.json'),JSON.stringify(result,null,2)+'\n')
console.log(JSON.stringify(result))
if(!result.verdict.proven||!result.verdict.checked||!result.retention.complete)throw Error('symbolic fixture failed to retain a proof')
const m=r.machine
if(JSON.stringify(m.params)!=='["size"]'||m.pre!==undefined)throw Error('symbolic fixture gained a size cap')
writeFileSync(join(out,'machine.json'),JSON.stringify(m,null,2)+'\n')
writeFileSync(join(out,'capture-sha256.txt'),result.retention.manifestSha256+'\n')
writeFileSync(join(out,'result.json'),JSON.stringify({fixture:true,givenHelpers:false,publicCalls:1,proven:true,checked:true,retention:result.retention,sizeParameter:'size',numericSizeCap:false},null,2)+'\n')
