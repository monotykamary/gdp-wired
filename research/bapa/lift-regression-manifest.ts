// Inventory frozen evidence; does not generate or check any proof.
import {existsSync,readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {auditLiftLog} from '../../lean-kernel/axiom-audit.ts'
import {readLiftSource,sourceStructure} from '../../lean-kernel/lift/source.ts'
import {assert,hashFile,json,type Entry,type Evidence,type Input,type Manifest} from './lift-regression.ts'
const base='research/bapa/'
const evidence=(path:string):Evidence=>({path,sha256:hashFile(path)})
export function inventory(inputs:Input[]):Manifest{
  assert(inputs.length===27&&new Set(inputs.map(e=>e.id)).size===27,'expected 27 unique accepted inputs')
  const entries:Entry[]=inputs.map(input=>{
    const dir=input.baselineDirectory,receiptPath=join(dir,'RELEASE-REPLAY.json'),r=json<any>(receiptPath)
    assert(r.status==='SOURCE_CHECKED'&&r.id===input.id,'baseline not accepted: '+input.id)
    assert((r.input?.captureSha256??r.inputSha256)===input.capture.sha256,'baseline capsule differs: '+input.id)
    const emissionPath=join(dir,'project/EMITTED.json'),m=existsSync(emissionPath)?json<any>(emissionPath):null
    if(m)assert(hashFile(emissionPath)===r.emissionSha256,'baseline emission hash differs: '+input.id)
    const familyTheorem=input.familyTheorem??m?.familyTheorem,sourceTheorems=input.sourceTheorems??m?.sourceProjection?.sourceTheorems
    assert(typeof familyTheorem==='string'&&Array.isArray(sourceTheorems)&&sourceTheorems.length>0,'missing historical theorem roles')
    const roles=[familyTheorem,...sourceTheorems]
    let logPaths:string[]
    if(r.commands){
      const command=r.commands.find((c:any)=>c.command?.join(' ')==='lake env lean BapaProof.lean')
      assert(command?.exitCode===0,'no successful native root check')
      logPaths=['lean.stdout.log','lean.stderr.log'].map(name=>join(dir,name))
      assert(hashFile(logPaths[0]!)===command.stdoutSha256&&hashFile(logPaths[1]!)===command.stderrSha256,'baseline root log changed')
    }else{
      const checkedPath=join(dir,'SOURCE-CHECKED.json')
      assert(hashFile(checkedPath)===r.sourceCheckSha256,'historical source-check receipt changed')
      const checked=json<any>(checkedPath)
      logPaths=['Checks.log','SdlSourceBridge.log'].map(name=>join(dir,name))
      for(const p of logPaths){const module=p.split('/').at(-1)!.replace(/\.log$/,'');assert(hashFile(p)===checked.modules[module].logSHA256,'historical module log changed')}
    }
    const rows=auditLiftLog(logPaths.map(p=>readFileSync(p,'utf8')).join('\n'),[],roles)
    const axioms=Object.fromEntries(roles.map(name=>[name,rows.find(row=>row.name===name)!.axioms]))
    const sourcePath=base+'lift-fixtures/'+input.id+'.json',pending:string[]=[]
    let source:Entry['source']={path:sourcePath,sha256:null,publicLawNames:null,status:'PENDING'}
    let historicalEncodedSourceMatches:boolean|undefined
    if(existsSync(sourcePath)){
      const fixture=readLiftSource(sourcePath)
      assert(fixture.source.id===input.id,'source fixture id differs')
      if(input.baselineSource){
        const b=input.baselineSource
        if('machine'in b){
          assert(m?.files&&hashFile(join(dir,b.machine))===m.files['source-machine.json']&&hashFile(join(dir,b.laws))===m.files['source-laws.json'],'historical source data changed')
        }
        const historical='combined'in b?json<any>(join(dir,b.combined)):{machine:json(join(dir,b.machine)),laws:json(join(dir,b.laws))}
        // Fresh constructor binders are preserved, not normalized into the historical AST.
        // Actual correspondence remains the job of the emitted native source bridge.
        historicalEncodedSourceMatches=sourceStructure({machine:fixture.source.machine,laws:fixture.source.laws})===sourceStructure({machine:historical.machine,laws:historical.laws})
      }else{
        const provenance=json<any>(base+'lift-fixtures/'+input.id+'.provenance.json')
        assert(provenance.captureSha256===input.capture.sha256&&provenance.sourceSha256===fixture.sourceSha256&&provenance.scope==='frozen-capsule-original','native source provenance differs')
      }
      const provenancePath=base+'lift-fixtures/'+input.id+'.provenance.json'
      const provenance=json<any>(provenancePath)
      assert(provenance.sourceSha256===fixture.sourceSha256,'fixture provenance hash differs')
      source={path:sourcePath,sha256:fixture.sourceSha256,publicLawNames:fixture.source.laws.map(l=>l.name),status:'FROZEN',historicalEncodedSourceMatches,provenance:evidence(provenancePath)}
    }else pending.push('source fixture missing: '+input.sourceScope)
    return {...input,source,baseline:{receipt:evidence(receiptPath),emission:m?evidence(emissionPath):null,logs:logPaths.map(evidence),familyTheorem,sourceTheorems,axioms},pending}
  })
  return {schema:'gdp-lift-regression/v1',allSizesProven:false,scope:'native fixtures freeze capsule.original; special fixtures must equal current accepted encoded source machine/laws. Source lifting is not independent TLA verification.',independentTlaVerification:false,entries}
}
if(import.meta.main){
  const manifest=inventory(json<Input[]>(base+'lift-regression-inputs.json'))
  writeFileSync(base+'lift-regression-manifest.json',JSON.stringify(manifest,null,2)+'\n')
  console.log(JSON.stringify({entries:manifest.entries.length,frozen:manifest.entries.filter(e=>!e.pending.length).length,pending:manifest.entries.filter(e=>e.pending.length).map(e=>({id:e.id,pending:e.pending}))},null,2))
}
