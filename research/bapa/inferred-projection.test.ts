import {expect,test} from 'bun:test'
import {atMost,n,type Law} from '../../core/machine.ts'
import {obligations,leafConstraints,type Tree} from '../../kernel/kernel.ts'
import {syntheticPlain} from './proof-synthetic.ts'
import {emitAlphaSource} from './source-projection.ts'
import type {ProvenanceBundle} from './proof-capture.ts'
function fixture():ProvenanceBundle {
 const p=syntheticPlain(),pub:Law={name:'public',holds:atMost(n(0),n(0))},laws=[p.laws[0]!,pub]
 const trees=Object.fromEntries(obligations(p.machine,laws).map(g=>{
  const rows=leafConstraints(g,new Map()),index=rows.findIndex(r=>Object.keys(r.lin).every(k=>k==='1')&&(r.lin['1']??0)>0)
  if(index<0)throw Error('fixture contradiction absent')
  return [g.name,{leaf:[{kind:'input',index}]} as Tree]
 }))
 const leaf={kind:'usual' as const,machine:p.machine,laws,proof:{instances:{},trees}}
 return {schema:'bapa-proof/v1',route:'inferred',identity:{} as ProvenanceBundle['identity'],original:{machine:p.machine,laws:[pub]},verdict:{proven:true,checked:true},terms:{terms:[],identities:[]},projection:{kind:'same-machine',publicLawIndices:[1]},proof:{kind:'derived',parents:[leaf],context:{kind:'inference'}}}
}
test('same-machine inferred projection keeps the full helper family and selects its public member',()=>{
 const text=emitAlphaSource('inferred',fixture())
 expect(text).toContain('def inferred_e0')
 expect(text).toContain('def inferred_e1')
 expect(text).toContain('inferred_source_law0 = inferred_e1.law')
 expect(text).toContain('inferred_source_laws')
 expect(text).not.toContain('sorry')
})
test('inferred projection refuses source mismatch and missing helper certificate',()=>{
 const b=fixture();b.original.machine={...b.original.machine,name:'changed'}
 expect(()=>emitAlphaSource('bad',b)).toThrow('same source machine')
 const c=fixture();if(c.proof.kind!=='derived'||c.proof.parents[0]?.kind!=='usual')throw Error('fixture')
 delete c.proof.parents[0].proof.trees['true law @step']
 expect(()=>emitAlphaSource('bad',c)).toThrow('does not check')
})
