import {expect,test} from 'bun:test'
import {createHash} from 'node:crypto'
import {readFileSync} from 'node:fs'
import {type Law,type Machine,n,same,x} from './machine.ts'
import {type CountCert,checkCountedLaws,countedObligations,mcGoal} from '../kernel/kernel.ts'
import {clock,grow,withDeadline,withWall} from '../kernel/prove.ts'
import {rescopeCountProof} from './count-proof-rescope.ts'
// Execute the verbatim f585 modules without modifying the checkout. Only
// import URLs change; the fixtures' original hashes are asserted below.
const fixture=(name:string)=>readFileSync(new URL('../research/track-m/section46-baseline-'+name+'.txt',import.meta.url),'utf8')
const scopeText=fixture('scope'),rescopeText=fixture('rescope')
const moduleURL=(source:string,scopeURL?:string)=>'data:text/javascript;base64,'+Buffer.from(new Bun.Transpiler({loader:'ts',target:'bun'}).transformSync(source.replace(/from '([^']+)'/g,(_,path:string)=>"from '"+(path==='./count-proof-scope.ts'&&scopeURL?scopeURL:new URL(path,import.meta.url).href)+"'"))).toString('base64')
const baselineModule=moduleURL(rescopeText,moduleURL(scopeText))
const {rescopeCountProof:baseline}=await import(baselineModule) as {rescopeCountProof:typeof rescopeCountProof}
const hashes=readFileSync(new URL('../research/track-m/section46-closure-gate/source-after.sha256',import.meta.url),'utf8')
for(const [text,path]of [[scopeText,'core/count-proof-scope.ts'],[rescopeText,'core/count-proof-rescope.ts']])expect(hashes).toContain(createHash('sha256').update(text!).digest('hex')+'  '+path)
test('accepted reduced family bytes and native verdict equal frozen f585',()=>withWall(performance.now()+10000,()=>withDeadline(clock()+10000,()=>{
 const until=clock()+9000,m:Machine={name:'fixed byte control',params:[],inputs:[],state:{a:n(0),b:n(0),noise:n(0)},step:{state:{a:x('b'),b:x('a')}}},a:Law={name:'left',holds:same(x('a'),n(0))},b:Law={name:'right',holds:same(x('b'),n(0))},noise:Law={name:'unused',holds:same(x('noise'),n(9))},family=[noise,a,b],closed=[a,b],oldCerts:Record<string,CountCert>={},newCerts:Record<string,CountCert>={},oldPremises:Record<string,readonly string[]>={},newPremises:Record<string,readonly string[]>={}
 for(const owner of closed){
  const certs:Record<string,CountCert>={};for(const {goal,decls}of countedObligations(m,family,{},family.indexOf(owner))){const base={reads:[],insts:[]},r=grow(mcGoal(goal.hyps,decls,base)!,new Map(),{nodes:0,until});if(!('tree'in r))throw Error('fixture did not close');certs[goal.name]={...base,tree:r.tree}}
  const proof={instances:{},certs,premises:family.map(l=>l.name)},before=JSON.stringify(proof),prior=baseline(m,owner,family,proof,new Set(closed.map(l=>l.name)),until)!,now=rescopeCountProof(m,owner,family,proof,new Set(closed.map(l=>l.name)),until)!
  expect(prior).toBeDefined();expect(now).toBeDefined();expect(JSON.stringify(proof)).toBe(before);Object.assign(oldCerts,prior.proof.certs);Object.assign(newCerts,now.proof.certs);oldPremises[owner.name]=prior.proof.premises!;newPremises[owner.name]=now.proof.premises!
 }
 const oldProof={instances:{},certs:oldCerts,premises:oldPremises},newProof={instances:{},certs:newCerts,premises:newPremises}
 expect(JSON.stringify(newProof)).toBe(JSON.stringify(oldProof));expect(checkCountedLaws(m,closed,oldProof)).toBe(true);expect(checkCountedLaws(m,closed,newProof)).toBe(true)
})))
