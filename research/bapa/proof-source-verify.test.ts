// Parser/custody controls only. The synthetic logs below are not Lean evidence.
import {expect,test} from 'bun:test'
import {createHash} from 'node:crypto'
import {mkdtempSync,writeFileSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {verifyCountedSourceProject} from './proof-source-verify.ts'
const source='#print axioms bapa_full_laws\n#print axioms bapa_public_holds\n',bridge='-- parser fixture\n'
const digest=(s:string)=>createHash('sha256').update(s).digest('hex')
const log="'bapa_full_laws' depends on axioms: [propext, Classical.choice, Quot.sound]\n'bapa_public_holds' depends on axioms: [propext, Classical.choice, Quot.sound]\nBuild completed successfully (2 jobs).\n"
function fixture(run:(root:string)=>void){
 const root=mkdtempSync(join(tmpdir(),'bapa-source-verify-'))
 try{
  writeFileSync(join(root,'BapaProof.lean'),source);writeFileSync(join(root,'CountedSourceBridge.lean'),bridge)
  writeFileSync(join(root,'EMITTED.json'),JSON.stringify({schema:'bapa-emission/v1',status:'EMITTED_NOT_CHECKED',inputSha256:'a'.repeat(64),leanExecuted:false,allSizesProven:false,familyTheorem:'bapa_full_laws',sourceProjection:{kind:'counted',sourceTheorems:['bapa_public_holds']},files:{'BapaProof.lean':digest(source),'CountedSourceBridge.lean':digest(bridge)}}))
  run(root)
 }finally{rmSync(root,{recursive:true,force:true})}
}
test('source receipt requires exact public names, not just an axiom-output count',()=>fixture(root=>{
 expect(verifyCountedSourceProject(root,log).status).toBe('SOURCE_CHECKED')
 expect(()=>verifyCountedSourceProject(root,log.replace('bapa_public_holds','bapa_unrelated'))).toThrow('missing exact theorem')
 expect(()=>verifyCountedSourceProject(root,log.replace('Quot.sound','Lean.ofReduceBool'))).toThrow('depends on')
 expect(()=>verifyCountedSourceProject(root,log.replace('Build completed successfully','Build failed'))).toThrow('no clean completed')
}))
test('source receipt refuses changed emitted files',()=>fixture(root=>{
 writeFileSync(join(root,'BapaProof.lean'),source+'-- changed\n')
 expect(()=>verifyCountedSourceProject(root,log)).toThrow('emitted file changed')
}))
