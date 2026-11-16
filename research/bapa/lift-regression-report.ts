// Re-audit downloaded artifacts. Missing/failed jobs are never silently omitted.
import {readFileSync} from 'node:fs'
import {basename,join,resolve} from 'node:path'
import {auditLiftLog,gate} from '../../lean-kernel/axiom-audit.ts'
import {assert,checkEmission,hash,hashFile,json,verifyFiles,type Manifest} from './lift-regression.ts'
const run=resolve(process.argv[2]??''),path='research/bapa/lift-regression-manifest.json',manifest=json<Manifest>(path)
assert(process.argv.length===3&&manifest.entries.length===27,'usage: lift-regression-report.ts RUN_DIRECTORY (all 27)')
const errors:{id:string;reason:string}[]=[],accepted:string[]=[],implementations=new Set<string>(),snapshots=new Set<string>()
for(const e of manifest.entries)try{
  assert(!e.pending.length&&e.source.sha256,'unfrozen fixture')
  const dir=join(run,'lift-'+e.id+'.files'),r=json<any>(join(dir,'LIFT-REGRESSION.json'))
  assert(r.id===e.id&&r.status==='SOURCE_CHECKED','native job did not accept')
  assert(r.noSearch===true&&r.allSizesProven===false&&r.independentTlaVerification===false,'incorrect scope claim')
  assert(r.manifestSha256===hashFile(path),'manifest changed or mixed suite versions')
  assert(r.input.source.sha256===e.source.sha256&&r.input.capture.sha256===e.capture.sha256,'receipt inputs differ')
  assert(r.implementationSha256===hash(JSON.stringify(r.implementationFiles)),'invalid implementation inventory')
  implementations.add(r.implementationSha256);snapshots.add(r.claimedSnapshot??'unclaimed')
  const project=join(dir,'project'),m=json<any>(join(project,'EMITTED.json'))
  assert(hashFile(join(project,'EMITTED.json'))===r.emissionSha256,'emission changed')
  checkEmission(e,m,e.source.sha256);verifyFiles(project,m.files)
  assert(JSON.stringify(r.files)===JSON.stringify(m.files),'receipt file inventory differs')
  assert(r.commands.length===2,'expected exactly build/root commands')
  for(const [i,expected]of [['lake','build'],['lake','env','lean','BapaProof.lean']].entries()){
    const command=r.commands[i]
    assert(JSON.stringify(command.argv)===JSON.stringify(expected)&&command.exitCode===0&&!command.signal&&!command.problem,'command not successful native check')
    for(const log of command.logs)assert(hashFile(join(dir,basename(log.path)))===log.sha256,'log changed')
  }
  const build=['lift-build.stdout.log','lift-build.stderr.log'].map(p=>readFileSync(join(dir,p),'utf8')).join('\n')
  assert(gate(build,[],false).length===0&&!/\berror:/.test(build),'invalid build log')
  const log=['lift-root.stdout.log','lift-root.stderr.log'].map(p=>readFileSync(join(dir,p),'utf8')).join('\n')
  const checked=auditLiftLog(log,[readFileSync(join(project,'BapaProof.lean'),'utf8')],m.requiredTheorems,e.baseline.axioms)
  assert(JSON.stringify(checked)===JSON.stringify(r.checkedTheorems),'checked theorem receipt differs from log')
  accepted.push(e.id)
}catch(error){errors.push({id:e.id,reason:error instanceof Error?error.message:String(error)})}
if(implementations.size!==1)errors.push({id:'suite',reason:'not one implementation inventory'})
if(snapshots.size!==1||snapshots.has('unclaimed'))errors.push({id:'suite',reason:'not one claimed frozen snapshot'})
const result={schema:'gdp-lift-regression-summary/v1',status:errors.length?'INCOMPLETE':'SOURCE_CHECKED',expected:27,accepted,errors,implementationSha256:[...implementations],claimedSnapshot:[...snapshots],allSizesProven:false,independentTlaVerification:false}
console.log(JSON.stringify(result,null,2));if(errors.length)process.exitCode=1
