import {expect,test} from 'bun:test'
import {mkdtempSync,writeFileSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {applyLiftTheoremNames} from './lift-names.ts'
import {readLiftSource,sha256} from './lift/source.ts'
function fixture(){
 const root='theorem generated_family : True := True.intro\ntheorem generated_source : True := True.intro\n#print axioms generated_family\n#print axioms generated_source\n'
 return {project:{'BapaProof.lean':root},manifest:{familyTheorem:'generated_family',sourceProjection:{sourceTheorems:['generated_source']},requiredTheorems:['generated_family','generated_source'],files:{'BapaProof.lean':sha256(root)}}}
}
test('output aliases preserve canonical targets and bind the changed root',()=>{
 const {project,manifest}=fixture(),out=applyLiftTheoremNames(project,manifest,{family:'Legacy.Checked.family',source:['legacy_source']})
 expect(out.theoremAliases?.family.target).toBe('generated_family')
 expect(out.sourceProjection.sourceTheorems).toEqual(['legacy_source'])
 expect(project['BapaProof.lean']).toContain('abbrev Legacy.Checked.family := @generated_family')
 expect(project['BapaProof.lean']).toContain('abbrev legacy_source := @generated_source')
 expect(out.requiredTheorems).toEqual(['generated_family','generated_source','Legacy.Checked.family','legacy_source'])
 expect(out.files['BapaProof.lean']).toBe(sha256(project['BapaProof.lean']))
})
test('existing generated names require an equality check, not blind reuse',()=>{
 const {project,manifest}=fixture()
 applyLiftTheoremNames(project,manifest,{family:'generated_source',source:['generated_family']})
 expect(project['BapaProof.lean']).toContain('example : @generated_source = @generated_family := rfl')
})
test('invalid alias contracts cannot inject code or omit a source law',()=>{
 for(const names of [{family:'valid',source:[]},{family:'bad\naxiom x : False',source:['s']},{family:'same',source:['same']},{family:'A..B',source:['s']}]){
  const {project,manifest}=fixture()
  expect(()=>applyLiftTheoremNames(project,manifest,names)).toThrow()
 }
})
test('source JSON accepts only validated naming metadata and keeps source data',()=>{
 const dir=mkdtempSync(join(tmpdir(),'lift-names-'))
 try{
  const file=join(dir,'source.json'),source={schema:'gdp-lift-source/v1',id:'source',machine:{name:'s',params:[],inputs:[],state:{},step:{state:{}}},laws:[{name:'safe',holds:{op:'and',xs:[]}}],theorems:{family:'Old.family',source:['old_source']}}
  writeFileSync(file,JSON.stringify(source))
  expect(readLiftSource(file).source.theorems).toEqual(source.theorems)
  writeFileSync(file,JSON.stringify({...source,theorems:{...source.theorems,source:['bad;name']}}))
  expect(()=>readLiftSource(file)).toThrow('theorem')
 }finally{rmSync(dir,{recursive:true,force:true})}
})
