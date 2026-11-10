// Original-admission family receipts. Per-helper evidence, never a joint gate.
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {strict as assert} from 'node:assert'
import {isDeepStrictEqual} from 'node:util'
const dir=process.argv[2];if(!dir)throw Error('BATCH required')
const hash=(x:string|Buffer)=>createHash('sha256').update(x).digest('hex'),lex=(a:string,b:string)=>a.localeCompare(b)
const placement=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8')),lines=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(s=>s.split('\t'))
assert.deepEqual(lines.map(r=>r[0]!).sort(lex),['original-0','original-1','original-2'])
const rows=lines.map(([name,exit])=>{
 assert(name);assert.equal(Number(exit),0);const place=placement[name];assert(place?.exclusive&&place.co_tenants===0&&place.cpu)
 const root=join(dir,'receipts',name),raw=join(root,'raw'),manifest=JSON.parse(readFileSync(join(root,'archive-manifest.json'),'utf8')),archive=readFileSync(join(root,'receipts.tar.gz'))
 assert.equal(hash(archive),manifest.sha256);assert.equal(archive.length,manifest.bytes)
 const familyBytes=readFileSync(join(raw,'family.json')),family=JSON.parse(familyBytes.toString()),frozenBytes=readFileSync(join(raw,'frozen-family.json')),comparison=JSON.parse(readFileSync(join(raw,'family-comparison.json'),'utf8'))
 assert.equal(comparison.familySha256,hash(familyBytes));assert.equal(comparison.frozenSha256,hash(frozenBytes));assert.equal(comparison.admissionSize,family.laws.length)
 const frozen=JSON.parse(frozenBytes.toString()),machineDifferentFields=[...new Set([...Object.keys(family.m),...Object.keys(frozen.m)])].filter(key=>!isDeepStrictEqual(family.m[key],frozen.m[key])),changedLawBodies=family.laws.filter((l:any)=>{const original=frozen.laws.find((f:any)=>f.name===l.name);return original&&!isDeepStrictEqual(l,original)}).map((l:any)=>l.name)
 assert.equal(family.originalHarness,true);assert.equal(family.generatorOnly,true);assert.deepEqual(family.suppliedLaws,[])
 const before=readFileSync(join(raw,'source.before.sha256'),'utf8'),restored=readFileSync(join(raw,'source.restored.sha256'),'utf8');assert.equal(before,restored)
 assert.equal(before.split('\n')[0]!.slice(0,64),hash(readFileSync(join(raw,'counts.before.ts'))))
 const text=readFileSync(join(dir,name+'.log'),'utf8'),records=text.split('\n').flatMap(line=>{try{const r=JSON.parse(line);return r.measurementVersion===3?[r]:[]}catch{return[]}})
 assert.deepEqual(records.map(r=>r.tag).sort(lex),Object.keys(family.targets).sort(lex))
 const arms=records.map(r=>{
  assert(['p1','rows','star'].includes(r.tag));assert.equal(r.familySize,family.laws.length);assert.equal(r.law,family.laws[family.targets[r.tag]].name)
  assert.equal(r.budget,6000);assert.equal(r.wallAllowance,7000);assert.equal(r.conditional,true)
  const saved=JSON.parse(readFileSync(join(raw,'owned',r.tag,'summary.json'),'utf8'))
  for(const key of ['tag','law','familySize','checked','units','wallMs'])assert.deepEqual(saved[key],r[key])
  return {side:r.tag,tag:r.tag,law:r.law,familySize:r.familySize,workerChecked:r.checked,withinPassLine:r.checked&&r.units<=6000&&r.wallMs<=7000,units:r.units,wallMs:r.wallMs}
 })
 return {name,placement:place,archiveSha256:manifest.sha256,logSha256:hash(text),familySha256:hash(familyBytes),comparison,machineDifferentFields,changedLawBodies,missingTargets:family.missingTargets,arms}
})
const report={iterationOnly:true,gateGreen:false,scope:'conditional helpers against observed original admission families',independentAuditPending:true,rows}
writeFileSync(join(dir,'original-families.json'),JSON.stringify(report,null,2)+'\n')
console.log(JSON.stringify({rows:rows.map(r=>({name:r.name,family:r.comparison.admissionSize,missing:r.comparison.missingFromAdmission,arms:r.arms})),gateGreen:false}))
