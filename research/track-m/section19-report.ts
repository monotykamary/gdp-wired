// Presentation-only derivation from already-audited consumers. No proof search.
import {readFileSync,writeFileSync,mkdtempSync} from 'node:fs'
import {join} from 'node:path'
import {homedir} from 'node:os'
import {strict as assert} from 'node:assert'
import {citationStage} from './section19-stage.ts'
import {statement} from './section16-statements.ts'
const s=JSON.parse(readFileSync(join(process.argv[2]!,'summary.json'),'utf8')),out=mkdtempSync(join(homedir(),'track-m-section19-report-'))
for(const r of s.rows){const cs=new Map<number,any>(r.consumerAudit.map((c:any)=>[c.id,c]));for(const e of r.records)for(const u of e.uses){if(typeof u.consumer==='number'){const c=cs.get(u.consumer);assert(c);u.stage=citationStage(c)}}}
const overview={researchOnly:true,inputSha256:s.inputSha256,rows:s.rows.map((r:any)=>({law:r.law,op:r.op,searchUnits:r.searchUnits,searchWallMs:r.searchWallMs,closed:r.closed,helperUnits:r.helperUnits,otherHelperUnits:r.otherHelperUnits,nonEmittedAttemptUnits:r.nonEmittedAttemptUnits,summaries:r.summaries,proofStages:Object.fromEntries(['closure','leaf','later-lemma','other'].map(stage=>[stage,r.records.filter((e:any)=>e.uses.some((u:any)=>u.kind==='checked-proof'&&u.stage===stage)).length])),consumerCalls:r.consumerCalls,auditedConsumers:r.consumerAudit.length,checkedConsumerProofs:r.consumerAudit.filter((c:any)=>c.checked).length}))}
const csv=['law,op,id,helper,kind,normalized_statement,target_checked,proof_cited,core_cited,decision_read,any_recorded_use,setup_units,failed_units,source_units,check_units,transport_units,total_units,uses']
for(const r of s.rows)for(const e of r.records)csv.push([r.law,r.op,e.id,e.helper,e.kind,statement({bound:e.statement})?.text,e.targetChecked,e.proofCited,e.coreCited,e.uses.some((u:any)=>u.kind==='decision'),e.anyObservedUse,e.units.setup,e.units.failed,e.units.source,e.units.check,e.units.transport,e.totalUnits,JSON.stringify(e.uses)].map(v=>'"'+String(v??'').replaceAll('"','""')+'"').join(','))
writeFileSync(join(out,'summary.json'),JSON.stringify(s,null,2)+'\n');writeFileSync(join(out,'overview.json'),JSON.stringify(overview,null,2)+'\n');writeFileSync(join(out,'citations.csv'),csv.join('\n')+'\n')
console.log(JSON.stringify({output:out,...overview}));const p=Bun.spawn([process.execPath,'research/track-m/pack-section10-archive.ts',join(out,'summary.json'),join(out,'overview.json'),join(out,'citations.csv')],{stdout:'inherit',stderr:'inherit'});assert.equal(await p.exited,0)
