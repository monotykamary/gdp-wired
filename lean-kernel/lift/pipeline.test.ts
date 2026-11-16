import {expect,test} from 'bun:test'
import {mkdtempSync,readFileSync,writeFileSync,existsSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {emitGenericLift,readLiftInput,type GenericLiftManifest} from './index.ts'
import {asked} from '../axiom-audit.ts'

function child(args:string[]):string {
  const p=Bun.spawnSync([process.execPath,join(import.meta.dir,'pipeline-fixture.ts'),...args],{stdout:'pipe',stderr:'pipe',timeout:20000})
  if(p.exitCode!==0)throw Error(new TextDecoder().decode(p.stderr))
  return new TextDecoder().decode(p.stdout)
}
test('full API emits independent ids in fresh workers and never claims a source check',()=>{
  const root=mkdtempSync(join(tmpdir(),'lift-pipeline-'))
  try {
    child(['prepare',root])
    const a=JSON.parse(child(['emit',root,'control'])) as GenericLiftManifest
    const b=JSON.parse(child(['emit',root,'toy_consensus_forall'])) as GenericLiftManifest
    expect(a.status).toBe('EMITTED_NOT_CHECKED');expect(a.leanExecuted).toBe(false)
    expect(a.sourceProjection.kind).toBe('alpha');expect(b.sourceProjection.kind).toBe('alpha')
    expect(a.familyTheorem).toBe('bapa_control_laws');expect(b.familyTheorem).toBe('bapa_toy_consensus_forall_laws')
    expect(a.capsuleSha256).toBe(b.capsuleSha256);expect(a.sourceSha256).not.toBe(b.sourceSha256)
    expect(a.sourceProjection.sourceTheorems).toEqual(['bapa_control_source_law0_holds'])
    expect(a.requiredTheorems).toContain(a.familyTheorem)
    expect(a.requiredTheorems).toContain(a.sourceProjection.sourceTheorems[0]!)
    expect(existsSync(join(root,'out-control/EMITTED.json'))).toBe(true)
    const requests=asked(readFileSync(join(root,'out-control/BapaProof.lean'),'utf8'))
    expect(new Set(requests).size).toBe(requests.length)
    expect(requests.filter(n=>n==='bapa_control_row_valid')).toHaveLength(1)
  } finally {rmSync(root,{recursive:true,force:true})}
})
test('full API refuses altered source before restoring terms or creating output',()=>{
  const root=mkdtempSync(join(tmpdir(),'lift-mutation-'))
  try {
    child(['prepare',root]);const file=join(root,'source.json'),raw=readFileSync(file,'utf8')
    for(const mutate of [(s:any)=>{s.machine.state.s.value=1},(s:any)=>{s.laws[0].keys=['changed']}]){
      const source=JSON.parse(raw);mutate(source);writeFileSync(file,JSON.stringify(source))
      // Common future orchestration may load an explicitly different source.
      expect(readLiftInput(join(root,'capture'),file).source.id).toBe('control')
      expect(()=>emitGenericLift(join(root,'capture'),file,join(root,'out'))).toThrow('differs')
      expect(existsSync(join(root,'out'))).toBe(false)
    }
    writeFileSync(file,raw)
    expect(()=>emitGenericLift(join(root,'capture'),file,join(root,'out'),{expectedManifestSha256:'0'.repeat(64)})).toThrow('binding mismatch')
    expect(existsSync(join(root,'out'))).toBe(false)
  } finally {rmSync(root,{recursive:true,force:true})}
})
