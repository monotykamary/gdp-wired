import {test,expect} from 'bun:test'
import {mkdtempSync,rmSync,unlinkSync,writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {hashFile} from './lift-regression.ts'
import {auditNativeCommandLogs,assertNativeLogReferences,assertSuccessfulJobs,combineReleaseReplays,type NativeSummary,type ReleaseManifest} from './release-0501-report.ts'

test('requires both exact native stdout/stderr references, never a vacuous list',()=>{
  const good=()=>['lift-build','lift-root'].map(prefix=>({logs:['stdout','stderr'].map(kind=>({path:'out/'+prefix+'.'+kind+'.log',sha256:'a'.repeat(64)}))}))
  expect(()=>assertNativeLogReferences(good())).not.toThrow()
  const a=good();a[0]!.logs=[];expect(()=>assertNativeLogReferences(a)).toThrow('both native')
  const b=good();b[1]!.logs.pop();expect(()=>assertNativeLogReferences(b)).toThrow('both native')
  const c=good();c[0]!.logs[1]=c[0]!.logs[0]!;expect(()=>assertNativeLogReferences(c)).toThrow('duplicate')
  const d=good();d[1]!.logs[0]!.path='out/other.log';expect(()=>assertNativeLogReferences(d)).toThrow('exact set differs')
  expect(()=>assertNativeLogReferences([])).toThrow('two native commands')
})
test('requires enclosing native jobs and their tests to finish successfully',()=>{
  const names=['lift-a','paxos-release-replay'],good=names.map(n=>n+'\t0\t1.0\tboat').join('\n')
  expect(()=>assertSuccessfulJobs(good,names)).not.toThrow()
  expect(()=>assertSuccessfulJobs(good.replace('paxos-release-replay\t0','paxos-release-replay\t1'),names)).toThrow('not successful')
  expect(()=>assertSuccessfulJobs(good+'\n'+good,names)).toThrow('duplicate')
  expect(()=>assertSuccessfulJobs(good.split('\n')[0]!,names)).toThrow('exact set differs')
})

test('hashes every fixed native log and refuses each changed or deleted file',()=>{
  const dir=mkdtempSync(join(tmpdir(),'release-native-logs-'))
  try{
    const commands=['lift-build','lift-root'].map(prefix=>({logs:['stdout','stderr'].map(kind=>{
      const name=prefix+'.'+kind+'.log';writeFileSync(join(dir,name),'accepted log\n');return {path:name,sha256:hashFile(join(dir,name))}
    })}))
    expect(()=>auditNativeCommandLogs(dir,commands)).not.toThrow()
    for(const command of commands)for(const log of command.logs){
      writeFileSync(join(dir,log.path),'accepted log\nchanged bytes\n')
      expect(()=>auditNativeCommandLogs(dir,commands)).toThrow('digest differs')
      writeFileSync(join(dir,log.path),'accepted log\n');unlinkSync(join(dir,log.path))
      expect(()=>auditNativeCommandLogs(dir,commands)).toThrow()
      writeFileSync(join(dir,log.path),'accepted log\n')
    }
  }finally{rmSync(dir,{recursive:true,force:true})}
})

function fixture(){
  const ids=Array.from({length:27},(_,i)=>'native-'+i)
  const expected={implementationSha256:'c'.repeat(64),snapshot:'d'.repeat(40),nativeManifestSha256:'a'.repeat(64),capsuleManifestSha256:'b'.repeat(64)}
  const manifest:ReleaseManifest={schema:'gdp-bapa-release-replays/v1',version:'0.50.1',nativeManifest:{path:'native.json',sha256:expected.nativeManifestSha256},paxosCapsule:{path:'capsule',sha256:expected.capsuleManifestSha256,acceptedCommit:'e'.repeat(40)},entries:[...ids.map(id=>({id,format:'native-data-only-lift'})),{id:'paxos_epr',format:'lean-source-capsule'}],bounded:[{id:'mldr',maxSize:64}],scope:'encoded source only'}
  const native:NativeSummary={schema:'gdp-lift-regression-summary/v1',status:'SOURCE_CHECKED',expected:27,accepted:ids,errors:[],implementationSha256:[expected.implementationSha256],claimedSnapshot:[expected.snapshot],allSizesProven:false,independentTlaVerification:false}
  const paxos={id:'paxos_epr' as const,status:'SOURCE_CHECKED' as const,claimedSnapshot:expected.snapshot,implementationSha256:expected.implementationSha256}
  return {manifest,native,paxos,expected}
}
function check(f=fixture()){return combineReleaseReplays(f.manifest,f.native,f.paxos,f.expected)}
test('combines 27 native cases and one distinct source capsule on one exact tree',()=>{
  const r=check();expect(r.accepted).toHaveLength(28);expect(r.formats).toEqual({nativeDataOnlyLift:27,leanSourceCapsule:1})
  expect(r.scope).toEqual({encodedSourceOnly:true,independentTlaVerification:false,paxosNativeDataOnlyLift:false,mldrMaxSize:64})
})
test('rejects mixed code inventories and release commits',()=>{
  const a=fixture();a.paxos.implementationSha256='0'.repeat(64);expect(()=>check(a)).toThrow('different base implementation')
  const b=fixture();b.paxos.claimedSnapshot='0'.repeat(40);expect(()=>check(b)).toThrow('different release snapshot')
  const c=fixture();c.native.claimedSnapshot=['0'.repeat(40)];expect(()=>check(c)).toThrow('native snapshot')
  const d=fixture();d.expected.snapshot='unclaimed';expect(()=>check(d)).toThrow('exact release commit')
})
test('rejects missing, duplicate, substituted and incomplete cases',()=>{
  const a=fixture();a.native.accepted.pop();expect(()=>check(a)).toThrow('native accepted cases')
  const b=fixture();b.native.accepted[1]=b.native.accepted[0]!;expect(()=>check(b)).toThrow('duplicate')
  const c=fixture();c.manifest.entries[27]!.id='mldr';expect(()=>check(c)).toThrow('source-capsule cases')
  const d=fixture();d.native.errors.push('failed');expect(()=>check(d)).toThrow('incomplete')
  const e=fixture();e.manifest.entries[0]!.format='lean-source-capsule';expect(()=>check(e)).toThrow('27 native')
})
test('rejects changed manifests and widened claims',()=>{
  const a=fixture();a.manifest.nativeManifest.sha256='0'.repeat(64);expect(()=>check(a)).toThrow('native manifest changed')
  const b=fixture();b.manifest.paxosCapsule.sha256='0'.repeat(64);expect(()=>check(b)).toThrow('Paxos capsule manifest changed')
  const c=fixture();c.manifest.bounded[0]!.maxSize=65;expect(()=>check(c)).toThrow('MLDR must remain bounded')
  const d=fixture();d.native.independentTlaVerification=true;expect(()=>check(d)).toThrow('overstates')
})
