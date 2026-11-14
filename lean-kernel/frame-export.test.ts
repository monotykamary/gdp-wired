import {expect,test} from 'bun:test'
import {type C,type E} from '../core/machine.ts'
import {type Lin,type Step} from '../core/solver.ts'
import {type Count,type FrameCut,type Goal,type Path,type Tree,canon,checkGoalLemmas,framePath,leafConstraints} from '../kernel/kernel.ts'
import {encode,encodeCounted,mcToLean,cmachineToLean,leanProject} from './emit.ts'
import {createHash} from 'node:crypto'
import {readFileSync} from 'node:fs'
import {familyCutFixture, brokenFamilyCut} from './family-cut-fixture.ts'
import {monoExportFixture} from '../research/track-m/mono-export-fixture.ts'
const x=(name:string):E=>({op:'var',name}),n=(value:number):E=>({op:'const',value})
const opLe={op:1,'1':-4},opGe={op:-1,'1':4},frame:FrameCut={when:[opLe,opGe],post:'after',pre:'before'}
const goal:Goal={name:'framed export',hyps:[{op:'<',a:x('before'),b:x('after')},{op:'=',a:x('op'),b:n(4)}]}
const counts:Count[]=[{v:'before',key:'k',below:n(2),body:{op:'get',map:'M',key:x('k')}},{v:'after',key:'k',below:n(2),body:{op:'if',c:{op:'=',a:x('op'),b:n(4)},then:{op:'get',map:'M',key:x('k')},else:n(0)}}]
const path=(...ls:Lin[]):Path=>new Map(ls.map(lin=>[canon(lin),{lin,holds:true}]))
const leaf=(p:Path,wanted:Lin[]):Tree=>{
 const rows=leafConstraints(goal,p),steps:Step[]=wanted.map(r=>{const index=rows.findIndex(x=>canon(x.lin)===canon(r));if(index<0)throw Error('missing fixture row');return {kind:'input',index}})
 return {leaf:[...steps,{kind:'combine',a:0,b:1,ma:1,mb:1}]}
}
const tree:Tree={split:opLe,yes:{split:opGe,yes:leaf(framePath([frame],[],path(opLe,opGe)),[{after:1,before:-1},{before:1,after:-1,'1':1}]),no:leaf(new Map([[canon(opLe),{lin:opLe,holds:true}],[canon(opGe),{lin:opGe,holds:false}]]),[{op:1,'1':-3},opGe])},no:leaf(new Map([[canon(opLe),{lin:opLe,holds:false}]]),[{op:-1,'1':5},opLe])}

test('framed leaves encode against the same rows the native checker sees',()=>{
 expect(checkGoalLemmas(goal,tree,[],[frame],counts)).toBe(true)
 const out=encodeCounted('framed',goal,{tree,frames:[frame]},['before','after','op','k'],['M'])
 expect(out.tree).toContain('.leafAt')
 expect(out.tree).toContain('(sp [(0, (-1)), (1, 1)] 0)')
})
test('empty frames preserve the legacy encoder byte for byte',()=>{
 const ex={name:goal.name,goal,tree:{leaf:[]} as Tree},a=encode(ex),b=encode(ex,false,true,undefined,undefined,false,false,{frames:[]})
 expect([a.tab,a.tree,a.hyps,a.cols]).toEqual([b.tab,b.tree,b.hyps,b.cols])
})
test('goal-local monotone export includes its independent auxiliary table and proof',()=>{
 const f=monoExportFixture(),source=mcToLean('mono',f.hyps,f.decls,f.cert)
 expect(source).toContain('def mono_monos : List MonoCut')
 expect(source).toContain('mono_frames mono_monos = true')
 expect(source).toContain('mcF_sound mono_hyps mono_decls mono_cert mono_frames mono_monos [] mono_check')
 expect(()=>mcToLean('bad_mono',f.hyps,f.decls,{...f.cert,monos:[{...f.cert.monos![0]!,tree:{leaf:[]}}]})).toThrow('does not check')
})

test('goal-local export uses mcF_sound and refuses an invalid frame',()=>{
 const hyps:C[]=[{op:'<',a:n(0),b:n(0)}],cert={reads:[],insts:[],tree:{leaf:[{kind:'input' as const,index:0}]}}
 expect(mcToLean('empty',hyps,[],cert)).toContain('mcF_sound empty_hyps')
 expect(()=>mcToLean('bad',hyps,[],{...cert,frames:[frame]})).toThrow('does not check')
})

test('complete cut-free projects retain every frozen-F library byte and file order',()=>{
 const baseline=JSON.parse(readFileSync(new URL('./compat/count-family-F/LIBRARY-SHA256.json',import.meta.url),'utf8')) as {keyOrder:string[],hashes:Record<string,string>}
 for(const file of ['-- ordinary cut-free file\n','-- comment mentions CEntryF and checkCMachineF\n','def noCuts_proof : List CEntry := []\n']){
  const project=leanProject(file)
  expect(Object.keys(project)).toEqual([...baseline.keyOrder,'Proofs.lean','lean-toolchain','lakefile.lean'])
  for(const name of baseline.keyOrder) expect(createHash('sha256').update(project[name]!).digest('hex')).toBe(baseline.hashes[name]!)
  expect(project['Proofs.lean']).toBe(file)
  expect(project['lean-toolchain']).toBe('leanprover/lean4:v4.34.0\n')
  const modules=[...baseline.keyOrder.map(name=>name.replace(/\.lean$/,'')),'Proofs']
  expect(project['lakefile.lean']).toBe(`import Lake\nopen Lake DSL\n\npackage proofs\n\n@[default_target]\nlean_lib Proofs where\n  roots := #[${modules.map(name=>'`'+name).join(', ')}]\n`)
 }
})
test('cut-free family emission and explicit empty cut lists select the old checker',()=>{
 const f=familyCutFixture('none'),a=cmachineToLean('plain',f.machine,f.laws,f.proof),empty=structuredClone(f.proof)
 for(const cert of Object.values(empty.certs)){cert.frames=[];cert.monos=[];cert.lins=[]}
 expect(cmachineToLean('plain',f.machine,f.laws,empty)).toBe(a)
 expect(a).toContain('plain_proof : List CEntry :=')
 expect(a).not.toContain('CEntryF')
})
for(const kind of ['frame','mono','linear'] as const)test(`family ${kind} cuts are carried and malformed auxiliaries remain negative controls`,()=>{
 const f=familyCutFixture(kind),before=JSON.stringify(f),bad=brokenFamilyCut(f)
 const source=cmachineToLean(`with_${kind}`,f.machine,f.laws,f.proof,[{what:'invalid auxiliary',certs:bad.certs}])
 expect(source).toContain(`with_${kind}_proof : List CEntryF :=`)
 expect(source).toContain('checkCMachineF')
 expect(source).toContain('cmachineF_sound')
 expect(source).toContain('= false := by decide +kernel')
 const project=leanProject(source)
 expect(project['CountMachine.lean']).toContain('theorem cmachineF_sound')
 expect(project['QAlpha.lean']).toContain('theorem cmachineF_sound')
 expect(JSON.stringify(f)).toBe(before)
})
test('alpha-renamed cut families use the cut-aware QAlpha transport',()=>{
 const f=familyCutFixture('frame',true),source=cmachineToLean('alpha',f.machine,f.laws,f.proof)
 expect(source).toContain('QAlpha.cmachineF_sound')
 expect(source).toContain('alpha_checkedMachine')
})
