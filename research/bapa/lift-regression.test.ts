import {describe,test,expect} from 'bun:test'
import {checkEmission,sameSet,type Entry} from './lift-regression.ts'
import {auditLiftLog} from '../../lean-kernel/axiom-audit.ts'
const e={id:'fixture',capture:{sha256:'cap'},source:{publicLawNames:['law']},baseline:{familyTheorem:'family',sourceTheorems:['source'],axioms:{family:['propext'],source:[]}}} as unknown as Entry
const make=()=>({schema:'gdp-lift-emission/v1',status:'EMITTED_NOT_CHECKED',capsuleSha256:'cap',sourceSha256:'src',sourceId:'fixture',allSizesProven:false,leanExecuted:false,familyTheorem:'family',requiredTheorems:['family','source'],sourceProjection:{sourceTheorems:['source'],publicLawNames:['law']}})
const log="'family' depends on axioms: [propext]\n'source' does not depend on any axioms\n"
describe('unified lift regression coverage',()=>{
 test('accepts exact legacy names and axioms',()=>{checkEmission(e,make(),'src');expect(auditLiftLog(log,[],['family','source'],e.baseline.axioms)).toHaveLength(2)})
 test('missing source cannot be filled by duplicate',()=>{expect(()=>sameSet(['source','source'],['source','other'],'source')).toThrow()})
 test('different family name is not rebased',()=>{const m=make();m.familyTheorem='replacement';expect(()=>checkEmission(e,m,'src')).toThrow('family')})
 test('changed source names fail',()=>{const m=make();m.sourceProjection.sourceTheorems=['different'];expect(()=>checkEmission(e,m,'src')).toThrow()})
 test('missing public law fails',()=>{const m=make();m.sourceProjection.publicLawNames=[];expect(()=>checkEmission(e,m,'src')).toThrow()})
 test('all-sizes claim fails',()=>{const m=make();m.allSizesProven=true;expect(()=>checkEmission(e,m,'src')).toThrow()})
 test('source hash mismatch fails',()=>{expect(()=>checkEmission(e,make(),'other')).toThrow()})
 test('required source coverage is mandatory',()=>{const m=make();m.requiredTheorems=['family'];expect(()=>checkEmission(e,m,'src')).toThrow()})
 test('historical aggregate is still required but is not a second law',()=>{
  const old={...e,baseline:{...e.baseline,sourceTheorems:['aggregate','source']}}
  const m=make();m.requiredTheorems.push('aggregate');checkEmission(old,m,'src')
  m.requiredTheorems.pop();expect(()=>checkEmission(old,m,'src')).toThrow('historical')
 })
 test('duplicate per-law metadata cannot fill coverage',()=>{const m=make();m.sourceProjection.sourceTheorems=['source','source'];expect(()=>checkEmission(e,m,'src')).toThrow()})
 test('standard axiom set changes fail too',()=>{expect(()=>auditLiftLog(log.replace('[propext]','[propext, Classical.choice]'),[],['family','source'],e.baseline.axioms)).toThrow()})
 test('native compiler axioms refused',()=>{expect(()=>auditLiftLog(log.replace('[propext]','[Lean.ofReduceBool]'),[],['family','source'],e.baseline.axioms)).toThrow()})
 test('missing exact answer refused',()=>{expect(()=>auditLiftLog(log,[],['family','missing'],e.baseline.axioms)).toThrow()})
 test('duplicate answer refused',()=>{expect(()=>auditLiftLog(log+log,[],['family','source'],e.baseline.axioms)).toThrow()})
})
