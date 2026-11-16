import {expect,test} from 'bun:test'
import {mkdirSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {n,x,atMost,type C,type Machine,type Law} from '../../core/machine.ts'
import {countedObligations,leafConstraints,mcGoal,type CountCert,type Tree} from '../../kernel/kernel.ts'
import {tryEmitBoundInclusion,type BoundInclusionInput} from './index.ts'
import {candidateBounds,eraseBound,publicCoverage,structuralWeakening,trueCondition} from './structural.ts'
const atom=(k:number):C=>({op:'=',a:x('a'),b:n(k)})
const or=(...xs:C[]):C=>({op:'or',xs})
const and=(...xs:C[]):C=>({op:'and',xs})
const options={weightLimit:1000000n,maxOutputBytes:32*1024*1024,maxFiles:500,heartbeats:200000000,recursionDepth:100000}
function fixture(aux=false):BoundInclusionInput {
 const cap=37,original:Machine={name:'opaque capsule label',params:['size'],inputs:[],state:{s:n(0)},step:{state:{s:x('s')}},pre:atMost(x('size'),n(cap)),counts:{empty:{j:'j',key:'n',below:n(0),body:n(0)}}}
 const laws:Law[]=[{name:'retained-only name',holds:atMost(n(1),n(1)),forall:'a',keys:['b']},...(aux?[{name:'helper only',holds:atMost(n(2),n(2)),forall:'a',keys:['b']}]:[])]
 const certs:Record<string,CountCert>={}
 for(const {goal,decls}of countedObligations(original,laws)){
   const partial={reads:[],insts:[]},g=mcGoal(goal.hyps,decls,partial)!
   const rows=leafConstraints(g,new Map()),i=rows.findIndex(r=>Object.keys(r.lin).every(k=>k==='1')&&(r.lin['1']??0)>0)
   if(i<0)throw Error('missing synthetic contradiction')
   const tree:Tree={leaf:[{kind:'input',index:i}]};certs[goal.name]={...partial,tree}
 }
 const source={...original,name:'independent supplied source label',pre:undefined}
 return {id:'bapa_opaque',bundle:{final:{machine:original,laws,proof:{certs,instances:{}}}},providedSourceAST:{schema:'gdp-lift-source/v1',id:'opaque',machine:source,laws:[{name:'independent public name',forall:'a',keys:['b'],holds:or(atMost(n(3),n(0)),laws[0]!.holds,atMost(n(7),n(0)))}]},options}
}
test('arbitrary nested disjunction subset, not hardcoded source paths',()=>{
 for(const ns of [[2,4,9],[8,3,0],[12,10,1]]){
  const [a,b,c]=ns.map(atom)
  expect(structuralWeakening(or(or(a!,b!),c!),or(atom(100),a!,or(c!,atom(101),b!)))).not.toBeNull()
 }
 expect(structuralWeakening(or(atom(1),atom(2)),or(atom(2),atom(3)))).toBeNull()
 expect(structuralWeakening(and(atom(1),atom(2)),atom(2))).not.toBeNull()
 expect(structuralWeakening(atom(1),and(atom(1),atom(2)))).toBeNull()
 expect(structuralWeakening(or(atom(1)),or(atom(4),atom(1)))).not.toBeNull()
 expect(structuralWeakening({op:'not',x:and(atom(1),atom(2))},{op:'not',x:and(atom(3),atom(1),atom(2))})).not.toBeNull()
 expect(structuralWeakening({op:'not',x:and(atom(3),atom(1),atom(2))},{op:'not',x:and(atom(1),atom(2))})).toBeNull()
})
test('bound is inferred from admitted precondition, not identity or value',()=>{
 const f=fixture(),s=f.providedSourceAST.machine,p=f.bundle.final.machine
 expect(candidateBounds(s,p)).toEqual([37])
 expect(eraseBound(p,37).pre).toEqual(trueCondition)
 const p2={...p,pre:and(p.pre!,atMost(x('size'),n(19)))}
 expect(candidateBounds(s,p2)).toEqual([])
 expect(()=>tryEmitBoundInclusion({...f,bundle:{final:{...f.bundle.final,machine:p2}}})).toThrow('unsupported')
})
test('full transformed family and exact supplied source conclusions',()=>{
 const f=fixture(true),out=tryEmitBoundInclusion(f)!
 expect(out.bound).toBe(37);expect(out.parts.familySize).toBe(2);expect(out.parts.primaryObligations).toBe(4)
 expect(out.publicLawIndices).toEqual([0]);expect(out.sourceTheorems).toEqual(['bapa_opaque_source_law0_holds'])
 expect(out.project['bapa_opaque_Defs.lean']).toContain('countedEntryF bapa_opaque_bound')
 expect(out.project['bapa_opaque_Defs.lean']).toContain('bapa_opaque_entry1_raw')
 expect(out.project['bapa_opaque_Entry1.lean']).toContain('cEntryCheckF')
 expect(out.project['BapaProof.lean']).toContain('bapa_counted_source_law')
 expect(out.project['BapaProof.lean']).toContain('holdsOver bapa_opaque_source_law0')
 expect(out.project['bapa_opaque_Defs.lean']).not.toContain('theorem bapa_opaque_retained_check')
 const dest=process.env.BOUND_INCLUSION_TINY
 if(dest){mkdirSync(dest);for(const [name,text]of Object.entries(out.project))writeFileSync(join(dest,name),text,{flag:'wx'})}
})
test('ids and public law names do not select bound or retained entry',()=>{
 const f=fixture();f.id='bapa_renamed';f.providedSourceAST.id='renamed';f.providedSourceAST.laws[0]!.name='renamed again'
 expect(tryEmitBoundInclusion(f)!.publicLawIndices).toEqual([0])
 expect(()=>tryEmitBoundInclusion({...f,id:'arbitrary'})).toThrow('prefix')
})
test('unsupported change, missing helper, reversed law and ambiguous coverage refuse',()=>{
 const f=fixture(true)
 const changed=structuredClone(f);changed.providedSourceAST.machine.step={...changed.providedSourceAST.machine.step,state:{s:n(1)}}
 expect(()=>tryEmitBoundInclusion(changed)).toThrow()
 const missing=fixture(true);delete missing.bundle.final.proof.certs['helper only @step']
 expect(()=>tryEmitBoundInclusion(missing)).toThrow('incomplete')
 const ambiguous=fixture(true);ambiguous.providedSourceAST.laws[0]!.holds=trueCondition
 expect(()=>tryEmitBoundInclusion(ambiguous)).toThrow('ambiguous')
 expect(()=>publicCoverage([{name:'x',holds:or(atom(1),atom(2))}],[{name:'x',holds:or(atom(1),atom(3))}],37)).toThrow()
})
