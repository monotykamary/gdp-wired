// No prover call: emit the unchanged p4 source in a named numerical basis.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {join} from 'node:path'
import {cmachineToLean} from '../../lean-kernel/emit.ts'
import {boundOf,witnessesOf} from '../../kernel/kernel.ts'
const hash=(x:string|Uint8Array)=>createHash('sha256').update(x).digest('hex')
const out=process.env.SUPERCOMPUTER_OUTPUT_DIR!
const input=new URL('../protocols/ic3syn/p2-paxos-source-input.ts',import.meta.url)
const expected='3063304ae3bf8d7c7cc9870c838f7f5da7ab916a96d3729a7ca0b8db5f5b1d76'
if(hash(readFileSync(input))!==expected)throw Error('atomic source identity mismatch')
if(hash(readFileSync(new URL('../protocols/ic3syn/common.ts',import.meta.url)))!=='d84face9091688872b001f28d0ff31f1180590c57bf944efe6b32168651cd324')throw Error('source common identity mismatch')
const {protocols}=await import(input.href)
const p=protocols.find((p:any)=>p.id==='paxos_epr'),rule=p.make(),source=rule.machine,laws=p.laws(rule)
const vars=new Set<string>(),maps=new Set<string>()
function visit(x:any):void{if(!x||typeof x!=='object')return;if(Array.isArray(x)){x.forEach(visit);return}if(x.op==='var')vars.add(x.name);if(x.op==='get')maps.add(x.map);Object.values(x).forEach(visit)}
visit(laws)
for(const law of laws){if(law.forall){vars.add(law.forall);vars.add(law.forall+'#')}law.keys?.forEach((v:string)=>vars.add(v))}
for(const [name,q] of Object.entries(source.step.flags??{}) as [string,any][]){vars.add('?'+name);if(q.op==='all'){boundOf(q).forEach(v=>vars.add(v));witnessesOf(name,q).forEach(v=>vars.add(v))}}
let definitions='',basis:unknown
cmachineToLean('unused_empty_family',source,[],{instances:{},certs:{}},[],{extraVars:[...vars],extraMaps:[...maps],after:b=>{
  const m={...source,counts:undefined,inputMaps:[...(source.inputMaps??[]),...Object.keys(source.counts??{})]}
  const law=laws[0]
  basis={vars:b.vars,maps:b.maps}
  definitions=`import CountMachine\nnamespace Bapa.PaxosEprAtomicSource\nopen Kern\ndef machine : SMachine := ${b.machine(m)}\ndef declarations : List CDecl := ${b.decls(source.counts)}\ndef admission : C := ${b.condition(source.assume)}\ntheorem machine_admission : machine.f.m.assume = admission := rfl\nabbrev sizeId : Nat := ${b.ix('size')}\ndef safety : SEntry := ⟨⟨${b.condition(law.holds)}, ${law.forall?'some '+b.ix(law.forall):'none'}⟩, ${law.forall?b.ix(law.forall+'#'):0}, [${(law.keys??[]).map(b.ix).join(', ')}], [], [], [], [], [], ([], [], .leaf [] [] [] []), ([], [], .leaf [] [] [] [])⟩\nend Bapa.PaxosEprAtomicSource\n`
  return ''
}})
const files={'PaxosEprAtomicDefs.lean':definitions,'source-machine.json':JSON.stringify(source,null,2)+'\n','source-laws.json':JSON.stringify(laws,null,2)+'\n','basis.json':JSON.stringify(basis,null,2)+'\n'}
for(const [name,text] of Object.entries(files))writeFileSync(join(out,name),text)
writeFileSync(join(out,'SOURCE-EMISSION.json'),JSON.stringify({status:'EMITTED_NOT_CHECKED',sourcePortSha256:expected,newProofSearches:0,files:Object.fromEntries(Object.entries(files).map(([n,t])=>[n,hash(t)]))},null,2)+'\n')
