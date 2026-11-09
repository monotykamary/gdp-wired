// Strict iteration receipt projection, never a merge-gate decision.
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {strict as assert} from 'node:assert'
const [dir,familyFile]=process.argv.slice(2);if(!dir||!familyFile)throw Error('BATCH FAMILY required')
const hash=(b:string|Buffer)=>createHash('sha256').update(b).digest('hex'),familySha256=hash(readFileSync(familyFile)),placement=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8'))
const expected=['overlap','rows','star','safety','p1'].flatMap(tag=>['ab','ba'].map(order=>`${tag}-${order}`)),lines=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(line=>line.split('\t'))
assert.deepEqual(lines.map(r=>r[0]).sort(),[...expected].sort())
const rows=lines.map(([name,exit])=>{
 assert(name);assert.equal(Number(exit),0)
 const text=readFileSync(join(dir,name+'.log'),'utf8'),records=text.split('\n').flatMap(line=>{try{const x=JSON.parse(line);return x.side?[x]:[]}catch{return[]}})
 assert.equal(records.length,2);const before=records.find(r=>r.side==='before'),after=records.find(r=>r.side==='after');assert(before&&after)
 const place=placement[name];assert(place&&place.exclusive===true&&place.co_tenants===0&&typeof place.cpu==='string'&&place.cpu.length>0)
 const receipt=join(dir,'receipts',name),manifest=JSON.parse(readFileSync(join(receipt,'archive-manifest.json'),'utf8')),archive=readFileSync(join(receipt,'receipts.tar.gz'))
 assert.equal(hash(archive),manifest.sha256);assert.equal(archive.length,manifest.bytes)
 const raw=join(receipt,'raw');assert.equal(readFileSync(join(raw,'family.sha256'),'utf8').trim().split(/\s+/)[0],familySha256)
 const side=(r:any)=>{
  const saved=JSON.parse(readFileSync(join(raw,r.side,r.tag,'summary.json'),'utf8'))
  for(const key of ['tag','law','familySize','units','searchUnits','checkUnits','wallMs','checked'])assert.deepEqual(saved[key],r[key])
  assert.equal(saved.measurementVersion,3);assert.equal(saved.budget,6000);assert.equal(saved.wallAllowance,7000);assert.equal(saved.generatorOnly,true);assert.deepEqual(saved.suppliedLaws,[])
  assert(Number.isFinite(saved.units)&&saved.units>=0&&Number.isFinite(saved.wallMs)&&saved.wallMs>=0)
  const sourceHashes=readFileSync(join(raw,r.side+'.sha256'),'utf8').trim().split('\n');assert.equal(sourceHashes.length,6);assert(sourceHashes.every(s=>/^[a-f0-9]{64}  core\//.test(s)))
  return {tag:r.tag,law:r.law,workerChecked:r.checked,units:r.units,wallMs:r.wallMs,searchWallMs:r.searchWallMs,checkWallMs:r.checkWallMs,sourceHashes}
 }
 const a=side(before),b=side(after);assert.equal(a.law,b.law);assert.equal(a.tag,b.tag)
 return {name,placement:place,archiveSha256:manifest.sha256,logSha256:hash(text),order:records.map(r=>r.side),before:a,after:b,workerCheckedLost:a.workerChecked&&!b.workerChecked,unitDelta:b.units-a.units,wallDelta:b.wallMs-a.wallMs}
})
const report={iterationOnly:true,gateGreen:false,independentAuditPending:true,familySha256,rows,workerCheckedLosses:rows.filter(r=>r.workerCheckedLost).map(r=>r.name)}
writeFileSync(join(dir,'lane-b-pairs.json'),JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({iterationOnly:true,rows:rows.length,workerCheckedLosses:report.workerCheckedLosses}))
