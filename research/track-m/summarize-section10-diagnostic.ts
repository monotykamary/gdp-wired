import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
const dir=process.argv[2],full=process.argv[3]==='full';if(!dir)throw new Error('DIR required')
const sum=(xs:number[])=>xs.reduce((a,b)=>a+b,0),near=(a:number,b:number)=>{if(Math.abs(a-b)>1e-7)throw new Error(`ledger mismatch ${a} ${b}`)}
const reports=[]
for(const name of ['star','overlap']){
 const r=JSON.parse(readFileSync(join(dir,name+(full?'-full':'')+'.json'),'utf8')),d=r.production,fs=d.frames
 for(const f of fs){if(f.end===undefined)throw new Error('unclosed span');near(f.units,f.end-f.start);near(f.units,f.exclusive+sum(fs.filter((c:any)=>c.parent===f.id).map((c:any)=>c.units)))}
 const owner=(f:any,kind:string):any=>{while(f){if(f.kind===kind)return f;f=fs[f.parent]}return undefined}
 const rows=fs.filter((f:any)=>f.kind==='row').map((row:any)=>{
  const members=fs.filter((f:any)=>owner(f,'row')===row),byKind:Record<string,number>={}
  for(const f of members)byKind[f.kind]=(byKind[f.kind]??0)+f.exclusive
  near(row.units,sum(Object.values(byKind)))
  const leaves=members.filter((f:any)=>f.kind==='leaf').map((leaf:any)=>{
   const mine=members.filter((f:any)=>owner(f,'leaf')===leaf),attempts=mine.filter((f:any)=>f.kind==='source-attempt'),outcomes:Record<string,number>={}
   let rawRefuted=0
   for(const a of attempts){const es=d.events.filter((e:any)=>e.frame===a.id),last=es.findLast((e:any)=>e.kind==='source-result'||e.kind==='source-cached'),key=last?.outcome??'no-result';outcomes[key]=(outcomes[key]??0)+1;if(es.some((e:any)=>e.kind==='source-query-result'&&e.query.why==='refuted, not unfolded'))rawRefuted++}
   return {id:leaf.id,parent:leaf.parent,path:leaf.meta.path,depth:leaf.meta.depth,ownUnits:sum(mine.map((f:any)=>f.exclusive)),inclusiveUnits:leaf.units,outcomes,sourceQueries:mine.filter((f:any)=>f.kind==='source-query').length,rawRefuted}
  })
  near(row.units,sum(leaves.map((l:any)=>l.ownUnits))+row.exclusive)
  return {meta:row.meta,units:row.units,overshoot:row.units-row.meta.granted,byKind,leaves}
 })
 const control=full?{law:r.production.label}:readFileSync(join(dir,name+'-control.log'),'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l)).find(l=>l.diagnostic)
 if(!full){const controlComplete=control.closureSteps.filter((e:any)=>e.stage==='closure-complete'),observedComplete=fs.filter((f:any)=>f.kind==='closure');if(controlComplete.length!==observedComplete.length)throw new Error('closure counts changed');for(let i=0;i<controlComplete.length;i++)near(controlComplete[i].total,observedComplete[i].units)}
 const sourceSummary=r.sources.reduce((a:Record<string,number>,s:any)=>(a[s.outcome]=(a[s.outcome]??0)+1,a),{}),report={law:control.law,revision:r.revision,controlMatches:full?undefined:true,finalCases:d.events.filter((e:any)=>e.kind==='case-final-results'),firstUnfinished:r.firstUnfinished,originalNumericModel:r.originalNumericModel??null,freshNumeric:{units:r.freshDiagnosticNumeric.units,valid:r.freshDiagnosticNumeric.valid,model:r.freshDiagnosticNumeric.model,violated:r.freshDiagnosticNumeric.violated},rows,sourceSummary}
 reports.push(report);writeFileSync(join(dir,name+(full?'-full':'')+'-ledger.json'),JSON.stringify(report,null,2)+'\n')
 const table=['# '+control.law+' — frozen terminal source queries','','These are independent diagnostic probes; their units are not charged to the original draw. See README.md for whether this is the terminal model or the preceding observed model. A refuted query must also pass the unchanged kernel check.','','| Index | Instance terms | Unit | Outcome | Units | Core |','|---:|---|---:|---|---:|---:|',...r.sources.map((s:any)=>`| ${s.index} | ${s.inst.terms.map(([z,id]:[number,string])=>z+'*'+id).join(' + ')} | ${s.inst.unit} | ${s.outcome} | ${s.units.toFixed(6)} | ${s.query.core?.length??'—'} |`),'','The exact path, numeric goal, complete model and source hypotheses are retained in '+name+(full?'-full':'')+'.json (recoverable from the checked archive).','', '## Read mapping','',...r.production.captures.find((c:any)=>c.id===r.captureId).cert.reads.map((v:any)=>'- `'+v[0]+'` = `'+v[1]+'['+JSON.stringify(v[2])+']`')].join('\n')+'\n'
 writeFileSync(join(dir,name+(full?'-full':'')+'-sources.md'),table)
 writeFileSync(join(dir,name+(full?'-full':'')+'-point.json'),JSON.stringify({firstUnfinished:r.firstUnfinished,terminalQuery:r.freshDiagnosticNumeric.query.why,terminalCore:r.freshDiagnosticNumeric.query.core,terminalModel:r.freshDiagnosticNumeric.model??null,sourceContext:r.sourceContext??null},null,2)+'\n')
}
writeFileSync(join(dir,'ledger-summary.json'),JSON.stringify(reports,null,2)+'\n')
console.log(JSON.stringify(reports.map(r=>({law:r.law,controlMatches:r.controlMatches,rows:r.rows.map((x:any)=>({units:x.units,overshoot:x.overshoot,byKind:x.byKind,leaves:x.leaves.map(({path:_path,...l}:any)=>l)})),sourceSummary:r.sourceSummary}))))
