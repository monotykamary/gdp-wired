// Strict iteration receipt projection, never a merge-gate decision.
import {existsSync,readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {strict as assert} from 'node:assert'
const lexical=(a:string|undefined,b:string|undefined)=>(a??'').localeCompare(b??'')
const [dir,familyFile,jobsFile]=process.argv.slice(2);if(!dir||!familyFile)throw Error('BATCH FAMILY [JOBS] required')
const hash=(b:string|Buffer)=>createHash('sha256').update(b).digest('hex'),familySha256=hash(readFileSync(familyFile)),placement=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8'))
const expected:string[]=jobsFile?JSON.parse(readFileSync(jobsFile,'utf8')).map((j:{name:string})=>j.name):['overlap','rows','star','safety','p1'].flatMap(tag=>['ab','ba'].map(order=>`${tag}-${order}`)),lines=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(line=>line.split('\t'))
assert.deepEqual(lines.map(r=>r[0]).sort(lexical),[...expected].sort(lexical))
const rows=lines.map(([name,exit])=>{
 assert(name);assert.equal(Number(exit),0)
 const text=readFileSync(join(dir,name+'.log'),'utf8'),records=text.split('\n').flatMap(line=>{try{const x=JSON.parse(line);return x.side?[x]:[]}catch{return[]}})
 const comparison=records[0]?.comparison??'combined',rosters:Record<string,string[]>={combined:['before','after'],refined:['before','after'],'pass-order':['before','after'],isolate:['base','before','after'],partition:['base','helpers','reconstruction','full']},roster=rosters[comparison];assert(roster);assert.deepEqual(records.map(r=>r.side).sort(lexical),[...roster].sort(lexical));assert(records.every(r=>(r.comparison??'combined')===comparison))
 const place=placement[name];assert(place&&place.exclusive===true&&place.co_tenants===0&&typeof place.cpu==='string'&&place.cpu.length>0)
 const receipt=join(dir,'receipts',name),manifest=JSON.parse(readFileSync(join(receipt,'archive-manifest.json'),'utf8')),archive=readFileSync(join(receipt,'receipts.tar.gz'))
 assert.equal(hash(archive),manifest.sha256);assert.equal(archive.length,manifest.bytes)
 const raw=join(receipt,'raw');assert.equal(readFileSync(join(raw,'family.sha256'),'utf8').trim().split(/\s+/)[0],familySha256)
 const side=(r:any)=>{
  const saved=JSON.parse(readFileSync(join(raw,r.side,r.tag,'summary.json'),'utf8'))
  for(const key of ['tag','law','familySize','units','searchUnits','checkUnits','wallMs','checked'])assert.deepEqual(saved[key],r[key])
  assert.equal(saved.measurementVersion,3);assert.equal(saved.budget,6000);assert.equal(saved.wallAllowance,7000);assert.equal(saved.generatorOnly,true);assert.deepEqual(saved.suppliedLaws,[])
  assert(Number.isFinite(saved.units)&&saved.units>=0&&Number.isFinite(saved.wallMs)&&saved.wallMs>=0)
  const sourceHashes=readFileSync(join(raw,r.side+'.sha256'),'utf8').trim().split('\n'),policyFiles=['core/count-cases.ts',...['guard-cases','field-bound-lemmas','row-cases','derivability-closure','field-demand'].map(name=>`core/count-recovery/${name}.ts`)]
  assert.equal(sourceHashes.length,6);assert(sourceHashes.every(s=>/^[a-f0-9]{64}  core\//.test(s)))
  assert.deepEqual(sourceHashes.map(s=>s.slice(66)).sort(lexical),policyFiles.sort(lexical))
  const sourceRoot=join(raw,r.side+'-source'),sourceBytesVerified=existsSync(sourceRoot)
  if(sourceBytesVerified)for(const line of sourceHashes)assert.equal(hash(readFileSync(join(sourceRoot,line.slice(66)))),line.slice(0,64))
  return {side:r.side,passOrder:r.passOrder??[0,1],policy:r.policy??(r.side==='before'?'base':'combined'),tag:r.tag,law:r.law,workerChecked:r.checked,withinPassLine:r.checked&&r.units<=6000&&r.wallMs<=7000,units:r.units,wallMs:r.wallMs,searchWallMs:r.searchWallMs,checkWallMs:r.checkWallMs,sourceHashes,sourceBytesVerified}
 }
 const arms=records.map(side),a=arms.find(r=>r.side===(roster.includes('base')?'base':'before'));assert(a);assert(arms.every(r=>r.law===a.law&&r.tag===a.tag));const b=arms.find(r=>r.side==='after')
 return {name,comparison,placement:place,archiveSha256:manifest.sha256,logSha256:hash(text),order:records.map(r=>r.side),arms,before:a,after:b,workerCheckedLost:arms.some(r=>a.workerChecked&&!r.workerChecked),unitDelta:b?b.units-a.units:null,wallDelta:b?b.wallMs-a.wallMs:null}
})
const report={iterationOnly:true,gateGreen:false,independentAuditPending:true,familySha256,rows,workerCheckedLosses:rows.filter(r=>r.workerCheckedLost).map(r=>r.name),outsidePassLine:rows.flatMap(r=>r.arms.filter(a=>a.workerChecked&&!a.withinPassLine).map(a=>({job:r.name,policy:a.policy,units:a.units,wallMs:a.wallMs})))}
writeFileSync(join(dir,'lane-b-pairs.json'),JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({iterationOnly:true,rows:rows.length,workerCheckedLosses:report.workerCheckedLosses}))
