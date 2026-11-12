import {type Law,type Machine,n,same,x,min} from '../../../core/machine.ts'
import {type CountCert,type Tree,countedObligations,mcGoal,termColumn} from '../../../kernel/kernel.ts'
import {grow} from '../../../kernel/prove.ts'
import {type CountLawProof,isCheckedReducedScope,snapshotCountScopeBinding} from '../../../core/count-proof-scope.ts'
import {rescopeCountProof} from '../../../core/count-proof-rescope.ts'
import {markConditionalProof,snapshotConditionalProofMark} from '../../../core/count-recovery/conditional-proof.ts'
export function nativeMetadataFixture(until:number){
 const m:Machine={name:'native diagnostic binding',params:[],inputs:[],state:{a:n(0),b:n(0),noise:n(0)},step:{state:{a:x('b'),b:x('a')}}}
 const a:Law={name:'left',holds:same(x('a'),n(0))},b:Law={name:'right',holds:same(x('b'),n(0))},noise:Law={name:'unrelated',holds:same(x('noise'),n(9))},family=[noise,a,b]
 const certs:Record<string,CountCert>={}
 for(const {goal,decls}of countedObligations(m,family,{},family.indexOf(a))){
  const base={reads:[],insts:[]},expanded=mcGoal(goal.hyps,decls,base)!
  const result=grow(expanded,new Map(),{nodes:0,until})
  if(!('tree'in result))throw Error('native metadata fixture did not close')
  certs[goal.name]={...base,tree:result.tree}
 }
 const proof:CountLawProof={instances:{},certs}
 const scoped=rescopeCountProof(m,a,family,proof,new Set(),until)
 if(!scoped?.checkedReduced||!isCheckedReducedScope(scoped,m,family))throw Error('native metadata fixture has no checked binding')
 const binding=snapshotCountScopeBinding(scoped.checkedReduced)
 if(!binding||!binding.context.length)throw Error('empty native diagnostic context')
 const cert=Object.values(scoped.proof.certs)[0]!
 const leaf=(tree:Tree):Tree=>'split'in tree?leaf(tree.yes):tree
 const markTree=leaf(cert.tree!),markGoal=scoped.sources[0]!
 // An untrusted proposer hint is data, not an accepted lemma certificate. Its
 // back-reference makes dropping the native lemma association detectable.
 const lemmas:Parameters<typeof markConditionalProof>[2]=[{when:[],cut:{},tree:markTree}]
 markConditionalProof(markGoal,markTree,lemmas)
 const mark=snapshotConditionalProofMark(markTree)
 if(!mark)throw Error('missing native subtree mark')
 const term=min(x('native-diagnostic-column'),n(17)),column=termColumn(term)
 return {m,family,scoped,markTree,markTreeAlias:markTree,markGoal,markLemmas:lemmas,holder:{yes:markTree,no:markTree},term,termAlias:term,column,
  expected:{column,context:binding.context.map(p=>({...p})),lawNames:binding.laws.map(l=>l.name),problem:binding.problem,scope:binding.scope,markGoalName:markGoal.name}}
}
