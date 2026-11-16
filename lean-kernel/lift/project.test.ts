import {expect,test} from 'bun:test'
import {leanLibrary} from '../library.ts'
import {leanProject} from '../emit.ts'
import {liftProject} from './project.ts'

test('cut-free lifts use one coherent current counted library',()=>{
 const body='theorem small : True := True.intro\n',project=liftProject(body,{name:'BapaProof'})
 for(const [file,text]of Object.entries(leanLibrary))expect(project[file]).toBe(text)
 expect(project['FamilyParts.lean']).toContain('CEntryF')
 expect(project['CountMachine.lean']).toContain('CEntryF')
 expect(project['BapaProof.lean']).toBe(body)
 expect(project['lakefile.lean']).toContain('`FamilyParts')
 expect(project['lakefile.lean']).toContain('`BapaProof')
})
test('lift factory does not change the legacy public emitter',()=>{
 const body='theorem small : True := True.intro\n',old=leanProject(body),lifted=liftProject(body)
 expect(old['CountMachine.lean']).not.toBe(lifted['CountMachine.lean'])
 expect(leanProject(body)['CountMachine.lean']).toBe(old['CountMachine.lean'])
 expect(old['FamilyParts.lean']).toBeUndefined()
 expect(leanProject('import FamilyParts\n')['FamilyParts.lean']).toBe(leanLibrary['FamilyParts.lean'])
 expect(leanProject(body,{currentFamily:true})['CountMachine.lean']).toBe(leanLibrary['CountMachine.lean'])
})
