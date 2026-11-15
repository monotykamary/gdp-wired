import {expect,test} from 'bun:test'
import {mkdirSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {syntheticCounted} from './proof-synthetic.ts'
import {n} from '../../core/machine.ts'
import type {FamilyBundle} from './proof-capture.ts'
import {countedSourceProject} from './proof-counted-source.ts'
function fixture():FamilyBundle {
 const data=syntheticCounted(false)
 const original=data.original
 const final={...data.final,machine:{...data.final.machine,counts:{...data.final.machine.counts,derived:{j:'derivedJ',key:'derivedKey',below:n(0),body:n(0)}}}}
 return {schema:'bapa-family/v1',route:'counted-family',identity:{} as FamilyBundle['identity'],original,final,terms:{terms:[],identities:[]},verdict:{proven:true,checked:true},publicLawIndices:[0],projection:{kind:'unqualified',reason:'fixture added derived count'}}
}
const options={weightLimit:1000000n,maxOutputBytes:32*1024*1024,maxFiles:500,heartbeats:200000000,recursionDepth:100000}
test('counted source project retains full split family, source declarations and checked correspondence',()=>{
 const output=countedSourceProject('sample',fixture(),options)
 expect(output.parts.familySize).toBe(1)
 expect(output.parts.primaryObligations).toBe(2)
 expect(output.publicLawIndices).toEqual([0])
 expect(output.project['BapaProof.lean']).toContain('bapa_counted_source_law')
 expect(output.project['BapaProof.lean']).toContain('sample_source_decls')
 expect(output.project['BapaProof.lean']).toContain('sample_source_shape')
 expect(output.project['CountedNoninterference.lean']).toContain('step_avoids_two')
 expect(output.project['sample_Complete.lean']).toContain('cmachineF_sound')
 const root=process.env.BAPA_COUNTED_SOURCE_TINY
 if(root){mkdirSync(root);for(const [name,text]of Object.entries(output.project))writeFileSync(join(root,name),text,{flag:'wx'})}
})
