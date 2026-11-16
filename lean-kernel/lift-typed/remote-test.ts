// Test-only current source fixture. Never imported by the production component.
import {readFileSync,writeFileSync,mkdirSync,existsSync} from 'node:fs'
import {join} from 'node:path'
import {readCertificateGraph} from '../lift/proof-codec.ts'
import {validateLegacyManifest,validateLegacyEnvelope} from '../lift-legacy.ts'
import {restoreTermPrelude} from '../lift/proof-prelude.ts'
import {tryTypedBoundSubstitution} from './index.ts'
import {deriveTypedRoles} from './roles.ts'
const out=process.env.SUPERCOMPUTER_OUTPUT_DIR!
const load=(dir:string)=>{const outer=validateLegacyManifest(JSON.parse(readFileSync(join(dir,'CAPTURE.json'),'utf8'))),metadata:[object,unknown][]=[];const data:any=readCertificateGraph(join(dir,'graph'),outer.graphManifestSha256,{maxBytes:536870912,maxNodes:4000000,maxStrings:200000,maxArrayLength:2000000,maxShards:2048},(o,m)=>metadata.push([o,m]));return {outer,data,metadata}}
if(existsSync('typed-toy')) { const toy=load('typed-toy');writeFileSync(join(out,'toy-ast.json'),JSON.stringify({original:toy.data.original,final:{phase:toy.data.final.phase,checked:toy.data.final.checked,machine:toy.data.final.machine,laws:toy.data.final.laws,proofKeys:Object.keys(toy.data.final.proof),instances:Object.keys(toy.data.final.proof.instances),certs:Object.keys(toy.data.final.proof.certs)}}));
}
if(existsSync('typed-sdl')) { const sdl=load('typed-sdl'),leaves:any[]=[],contexts:any[]=[];const visit=(n:any,path:number[])=>{if(n.kind==='derived'){contexts.push({path,context:n.context});n.parents.forEach((p:any,i:number)=>visit(p,[...path,i]))}else leaves.push({path,kind:n.kind,machine:n.machine,laws:n.laws,proofKeys:Object.keys(n.proof),coverTrees:n.proof.coverTrees??n.coverTrees})};visit(sdl.data.proof,[]);writeFileSync(join(out,'sdl-ast.json'),JSON.stringify({original:sdl.data.original,contexts,leaves}));
}
const client=load('typed-client'),bundle=validateLegacyEnvelope(client.outer,client.data);restoreTermPrelude(bundle.terms,client.metadata)
const source = process.env.TYPED_SOURCE ? JSON.parse(readFileSync(process.env.TYPED_SOURCE,'utf8')) : await (async()=>{
 const {protocols}=await import('../../research/protocols/ic3syn/models.ts')
 const p=protocols.find(p=>p.id==='client_server_db_ae')!,r=p.make()
 return {schema:'gdp-lift-source/v1' as const,id:'anonymous_typed_fixture',machine:r.machine,laws:p.laws(r)}
})()
writeFileSync(join(out,'source.json'),JSON.stringify(source,null,2))
let leaf:any=client.data.proof;while(leaf.kind==='derived')leaf=leaf.parents[0]
writeFileSync(join(out,'roles-preflight.json'),JSON.stringify(deriveTypedRoles(source,client.data.original,leaf.machine,leaf.laws),null,2))
const result=tryTypedBoundSubstitution({id:'bapa_anonymous_typed_fixture',bundle,providedSourceAST:source,options:{weightLimit:1000000n,maxOutputBytes:268435456,maxFiles:20000,heartbeats:0,recursionDepth:100000}})
if(!result)throw Error('fixture was not a typed candidate')
writeFileSync(join(out,'roles.json'),JSON.stringify(result.roles,null,2));mkdirSync(join(out,'project'))
result.project['TypedControls.lean']=readFileSync(new URL('./TypedControls.lean',import.meta.url),'utf8')
if(result.roles.sizes.length>1)result.project['BapaProof.lean'] += `\ndef roleSwapTyping : Bapa.CertificateBoundSubstitution.Typed.Typing := {bapa_anonymous_typed_fixture_baseTyping with variables := bapa_anonymous_typed_fixture_baseTyping.variables.map fun (v,s) => (v, if s == bapa_anonymous_typed_fixture_baseTyping.sizes[0]! then bapa_anonymous_typed_fixture_baseTyping.sizes[1]! else s)}\ndef roleSwapMachine : Kern.SMachine := (Bapa.CertificateBoundSubstitution.Typed.machine ${result.roles.bound} roleSwapTyping bapa_anonymous_typed_fixture_retained_machine).getD bapa_anonymous_typed_fixture_retained_machine\ntheorem role_swap_complete_checker_refuses : Kern.checkSMachine roleSwapMachine bapa_anonymous_typed_fixture_proof = false := by decide +kernel\n#print axioms role_swap_complete_checker_refuses\n`
result.requiredTheorems.push('role_swap_complete_checker_refuses')
result.project['lakefile.lean'] += '\nlean_lib TypedControlChecks where\n  roots := #[`TypedControls]\n'
for(const [name,text]of Object.entries(result.project))writeFileSync(join(out,'project',name),text)
writeFileSync(join(out,'required.json'),JSON.stringify(result.requiredTheorems,null,2))
console.log('EMITTED',result.sourceTheorems)
