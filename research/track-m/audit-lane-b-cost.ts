// Independent checker-only replay of one conditional generated-family target.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {strict as assert} from 'node:assert'
import {checkMC,countedObligations,termColumn} from '../../kernel/kernel.ts'
import {fullWork,fullRate} from '../../kernel/prove.ts'
const p=JSON.parse(gunzipSync(readFileSync(process.argv[2]!)).toString()),r=p.record
assert.equal(r.conditional,true)
if(r.diagnostic==='section16.5'){assert.equal(r.generatorOnly,true);assert.deepEqual(r.suppliedLaws,[]);assert.equal(r.budget,6000);assert.equal(r.wallAllowance,7000)}else{assert.equal(r.budget,2700);assert.equal(r.wallAllowance,4800)}
for(const [i,t]of p.columns.entries())assert.equal(termColumn(t),`⟦${i}⟧`)
const index=p.laws.findIndex((l:any)=>l.name===r.law);assert(index>=0);assert.equal(r.familySize,p.laws.length)
const familyFile=process.argv[3]
if(familyFile){const family=JSON.parse(readFileSync(familyFile,'utf8'));assert.equal(family.originalHarness,true);assert.equal(family.generatorOnly,true);assert.deepEqual(family.suppliedLaws,[]);assert.deepEqual(p.m,family.m);assert.deepEqual(p.laws,family.laws);assert.equal(family.targets[r.tag],index)}
const replayCheckStart=fullWork(),obligations=countedObligations(p.m,p.laws,{[r.law]:p.proof?.instances??{}},index);assert.equal(obligations.length,2)
const checked=!!p.proof&&obligations.every(({goal,decls})=>{const cert=p.proof.certs[goal.name];return !!cert&&checkMC(goal.hyps,decls,cert)})
const replayCheckUnits=(fullWork()-replayCheckStart)/fullRate
assert.equal(checked,r.checked)
assert(r.results.length<=2);assert(r.results.every((x:any)=>x.units>=0));assert(r.units+1e-5>=r.results.reduce((n:number,x:any)=>n+x.units,0))
console.log(JSON.stringify({conditional:true,familyVerified:!!familyFile,originalHarness:!!familyFile,tag:r.tag,law:r.law,checked,units:r.units,searchUnits:r.searchUnits??r.units,replayCheckUnits,unitsWithReplayCheck:r.measurementVersion>=3?r.units:r.units+replayCheckUnits,wallMs:r.wallMs,unitsAboveRequested:Math.max(0,r.units-r.budget),results:r.results,completionTuples:r.events.filter((e:any)=>e.phase==='count-completion').flatMap((e:any)=>e.added??[])}))
