import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
const directory=process.argv[2];assert(directory)
const all=[1,2,3].map(rep=>{
 const text=readFileSync(join(directory,'mini-phase-contract-'+rep+'.log'),'utf8')
 const matches=text.split('\n').filter(line=>line.startsWith('MINI_PHASE_CONTRACT ')).map(line=>JSON.parse(line.slice('MINI_PHASE_CONTRACT '.length)))
 assert.equal(matches.length,1);const row=matches[0]
 assert.equal(row.passed,true);assert.equal(row.repetition,rep);assert.equal(row.fixtureAllowance,100000)
 assert.equal(row.source,'aeef60912e189573eb24e658af7e915109a971d2');assert.equal(row.cases.length,58)
 const keys=new Set<string>(),ids=new Set<string>()
 for(const item of row.cases){assert.equal(item.repetition,rep);assert(['original','broken'].includes(item.variant));assert(/^[a-f0-9]{64}$/.test(item.signatureSha256));assert(item.events>0);assert.equal(item.fitRows,item.events);assert(item.phases.includes('original-protocol'));keys.add(item.id+':'+item.variant);ids.add(item.id)}
 assert.equal(keys.size,58);assert.equal(ids.size,29)
 return row
})
const summary=readFileSync(join(directory,'summary.tsv'),'utf8').trim().split('\n').map(line=>line.split('\t'))
for(const rep of [1,2,3])assert(summary.some(([name,code])=>name==='mini-phase-contract-'+rep&&code==='0'))
const signatures=all.map(row=>row.cases.map((c:any)=>({id:c.id,variant:c.variant,signatureSha256:c.signatureSha256})))
assert.deepEqual(signatures[0],signatures[1]);assert.deepEqual(signatures[0],signatures[2])
for(const row of all){assert.deepEqual(row.diagnosticWeights,all[0].diagnosticWeights);assert.equal(row.childSha256,all[0].childSha256);assert.equal(row.kitSha256,all[0].kitSha256)}
const eprCases=all[0].cases.filter((c:any)=>c.epr>0).map((c:any)=>({id:c.id,variant:c.variant,epr:c.epr}))
console.log('MINI_PHASE_CONTRACT_AUDIT '+JSON.stringify({passed:true,cases:174,source:all[0].source,kitSha256:all[0].kitSha256,childSha256:all[0].childSha256,deterministic:true,diagnosticWeights:all[0].diagnosticWeights,signatureSha256:createHash('sha256').update(JSON.stringify(signatures[0])).digest('hex'),eprCases,scope:'small-allowance transport/ledger compatibility, NOT mini calibration or full ordinary/EPR qualification'}))
