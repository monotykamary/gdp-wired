// Independent checker-only replay of one conditional generated-family target.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {strict as assert} from 'node:assert'
import {checkMC,countedObligations,termColumn} from '../../kernel/kernel.ts'
const p=JSON.parse(gunzipSync(readFileSync(process.argv[2]!)).toString()),r=p.record
assert.equal(r.conditional,true);assert.equal(r.budget,2700);assert.equal(r.wallAllowance,4800)
for(const [i,t]of p.columns.entries())assert.equal(termColumn(t),`⟦${i}⟧`)
const index=p.laws.findIndex((l:any)=>l.name===r.law);assert(index>=0)
const checked=!!p.proof&&countedObligations(p.m,p.laws,{[r.law]:p.proof.instances},index).every(({goal,decls})=>{const cert=p.proof.certs[goal.name];return !!cert&&checkMC(goal.hyps,decls,cert)})
assert.equal(checked,r.checked)
assert(r.results.length<=2);assert(r.results.every((x:any)=>x.units>=0));assert(r.units+1e-5>=r.results.reduce((n:number,x:any)=>n+x.units,0))
console.log(JSON.stringify({conditional:true,tag:r.tag,law:r.law,checked,units:r.units,wallMs:r.wallMs,unitsAboveRequested:Math.max(0,r.units-r.budget),results:r.results,completionTuples:r.events.filter((e:any)=>e.phase==='count-completion').flatMap((e:any)=>e.added??[])}))
