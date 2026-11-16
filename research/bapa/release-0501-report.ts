// One release tree, two explicit proof formats. This does not add a native Paxos lift adapter.
import {spawnSync} from 'node:child_process'
import {readFileSync} from 'node:fs'
import {basename,join,resolve} from 'node:path'
import {assert,hash,hashFile,implementationFiles,json,sameSet} from './lift-regression.ts'
import {auditPaxosReplay} from './paxos-release-audit.ts'

export type ReleaseManifest={
  schema:string;version:string
  nativeManifest:{path:string;sha256:string}
  paxosCapsule:{path:string;sha256:string;acceptedCommit:string}
  entries:{id:string;format:string}[]
  bounded:{id:string;maxSize:number}[]
  scope:string
}
export type NativeSummary={schema:string;status:string;expected:number;accepted:string[];errors:unknown[];implementationSha256:string[];claimedSnapshot:string[];allSizesProven:boolean;independentTlaVerification:boolean}
type PaxosSummary=Pick<ReturnType<typeof auditPaxosReplay>,'id'|'status'|'claimedSnapshot'|'implementationSha256'>
type Expected={implementationSha256:string;snapshot:string;nativeManifestSha256:string;capsuleManifestSha256:string}

// The historical 27-case reader hashes listed logs; require an exact, non-vacuous list first.
export function assertNativeLogReferences(commands:{logs?:{path:string;sha256:string}[]}[]){
  assert(Array.isArray(commands)&&commands.length===2,'expected two native commands')
  for(const [i,prefix] of ['lift-build','lift-root'].entries()){
    const logs=commands[i]?.logs
    assert(Array.isArray(logs)&&logs.length===2,'expected both native command log references')
    assert(logs.every(l=>typeof l.path==='string'),'invalid native log path')
    sameSet(logs.map(l=>basename(l.path)),[prefix+'.stdout.log',prefix+'.stderr.log'],'native command log names')
  }
}

export function auditNativeCommandLogs(directory:string,commands:{logs?:{path:string;sha256:string}[]}[]){
  assertNativeLogReferences(commands)
  for(const command of commands)for(const log of command.logs!)
    assert(hashFile(join(directory,basename(log.path)))===log.sha256,'native command log digest differs: '+basename(log.path))
}

// Proof SOURCE_CHECKED alone is insufficient if the enclosing job or its negative tests failed.
export function assertSuccessfulJobs(summary:string,expectedNames:string[]){
  const rows=summary.trim().split('\n').filter(Boolean).map(line=>line.split('\t'))
  for(const row of rows)assert(row.length>=4&&row[1]==='0','native job not successful: '+(row[0]??'missing'))
  sameSet(rows.map(row=>row[0]!),expectedNames,'successful native jobs')
}

export function combineReleaseReplays(manifest:ReleaseManifest,native:NativeSummary,paxos:PaxosSummary,expected:Expected){
  assert(manifest.schema==='gdp-bapa-release-replays/v1'&&manifest.version==='0.50.1','not the 0.50.1 release manifest')
  assert(/^[0-9a-f]{40}$/.test(expected.snapshot),'an exact release commit is required')
  assert(manifest.nativeManifest.sha256===expected.nativeManifestSha256,'native manifest changed')
  assert(manifest.paxosCapsule.sha256===expected.capsuleManifestSha256,'Paxos capsule manifest changed')
  assert(manifest.entries.length===28,'expected exactly 28 release cases')
  const nativeIds=manifest.entries.filter(e=>e.format==='native-data-only-lift').map(e=>e.id)
  const sourceIds=manifest.entries.filter(e=>e.format==='lean-source-capsule').map(e=>e.id)
  assert(nativeIds.length===27,'expected 27 native-data-only cases')
  sameSet(sourceIds,['paxos_epr'],'source-capsule cases')
  sameSet(manifest.entries.map(e=>e.id),[...nativeIds,'paxos_epr'],'all release cases')
  assert(JSON.stringify(manifest.bounded)===JSON.stringify([{id:'mldr',maxSize:64}]),'MLDR must remain bounded to 64')
  assert(native.schema==='gdp-lift-regression-summary/v1'&&native.status==='SOURCE_CHECKED'&&native.expected===27&&!native.errors.length,'native replay suite incomplete')
  assert(native.allSizesProven===false&&native.independentTlaVerification===false,'native summary overstates independent specification coverage')
  sameSet(native.accepted,nativeIds,'native accepted cases')
  sameSet(native.implementationSha256,[expected.implementationSha256],'native implementation')
  sameSet(native.claimedSnapshot,[expected.snapshot],'native snapshot')
  assert(paxos.id==='paxos_epr'&&paxos.status==='SOURCE_CHECKED','Paxos source replay incomplete')
  assert(paxos.implementationSha256===expected.implementationSha256,'Paxos uses a different base implementation')
  assert(paxos.claimedSnapshot===expected.snapshot,'Paxos uses a different release snapshot')
  return {schema:'gdp-bapa-release-summary/v1',status:'SOURCE_CHECKED',version:'0.50.1',expected:28,
    accepted:[...native.accepted,paxos.id],implementationSha256:expected.implementationSha256,claimedSnapshot:expected.snapshot,
    formats:{nativeDataOnlyLift:27,leanSourceCapsule:1},paxosCapsuleManifestSha256:expected.capsuleManifestSha256,
    scope:{encodedSourceOnly:true,independentTlaVerification:false,paxosNativeDataOnlyLift:false,mldrMaxSize:64}}
}

if(import.meta.main){
  try{
    assert(process.argv.length===3,'usage: release-0501-report.ts RUN_DIRECTORY')
    const root=process.cwd(),run=resolve(process.argv[2]!),manifestPath=join(root,'research/bapa/release-0501-manifest.json')
    const manifest=json<ReleaseManifest>(manifestPath)
    const nativeIds=manifest.entries.filter(e=>e.format==='native-data-only-lift').map(e=>e.id)
    assertSuccessfulJobs(readFileSync(join(run,'summary.tsv'),'utf8'),[...nativeIds.map(id=>'lift-'+id),'paxos-release-replay'])
    for(const id of nativeIds){const dir=join(run,'lift-'+id+'.files');auditNativeCommandLogs(dir,json<{commands:{logs?:{path:string;sha256:string}[]}[]}>(join(dir,'LIFT-REGRESSION.json')).commands)}
    const checked=spawnSync(process.execPath,[join(root,'research/bapa/lift-regression-report.ts'),run],{cwd:root,encoding:'utf8',maxBuffer:4*1024*1024})
    assert(!checked.error&&!checked.signal,'native audit did not complete')
    const native=JSON.parse(checked.stdout) as NativeSummary
    assert(checked.status===0,'native audit failed: '+JSON.stringify(native.errors))
    const paxosDir=join(run,'paxos-release-replay.files'),paxos=auditPaxosReplay(paxosDir,root)
    const summary=combineReleaseReplays(manifest,native,paxos,{implementationSha256:hash(JSON.stringify(implementationFiles(root))),snapshot:process.env.LIFT_REGRESSION_SNAPSHOT??'',nativeManifestSha256:hashFile(join(root,manifest.nativeManifest.path)),capsuleManifestSha256:hashFile(join(root,manifest.paxosCapsule.path,'SHA256SUMS'))})
    console.log(JSON.stringify({...summary,releaseManifestSha256:hashFile(manifestPath),paxosReplayReceiptSha256:hashFile(join(paxosDir,'PAXOS-REPLAY.json'))},null,2))
  }catch(error){
    console.log(JSON.stringify({schema:'gdp-bapa-release-summary/v1',status:'INCOMPLETE',expected:28,errors:[error instanceof Error?error.message:String(error)]},null,2))
    process.exitCode=1
  }
}
