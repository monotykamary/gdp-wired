import {expect, test} from 'bun:test'
import {atMost, n, x} from '../machine.ts'
import {type Goal, type Path, type Tree, canon, check, leafConstraintsReusing as rowsAt} from '../../kernel/kernel.ts'
import {conditionalProofStats, slicedCheck} from './conditional-check-cache.ts'

const goal = (): Goal => ({name: 'sliced pre-check', hyps: [atMost(x('unused'), n(9)), atMost(x('a'), n(0)), atMost(n(1), x('a'))]})
const proof = (): Tree => ({leaf: [{kind: 'input', index: 1}, {kind: 'input', index: 2}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]})
test('sliced leaves retain exact proof semantics and memoize the same immutable leaf', () => {
 const g=goal(), t=proof(), p=new Map(), before=conditionalProofStats()
 expect(check(g,t,p)).toBe(true);expect(slicedCheck(g,t,p)).toBe(true);expect(slicedCheck(g,t,p)).toBe(true)
 const after=conditionalProofStats();expect(after.leafHits-before.leafHits).toBe(1);expect(after.sliceHyps-before.sliceHyps).toBe(2)
})
test('sliced leaves retain square/product offsets and unused product dependencies', () => {
 const g=goal(), p:Path=new Map(), rows=rowsAt(g,p)
 const t:Tree={...proof(),squares:[{a:1}],products:[[1,2],[rows.length,rows.length+1]]}
 expect(check(g,t,p)).toBe(true);expect(slicedCheck(g,t,p)).toBe(true)
})
test('malformed leaves refuse and unused product handling matches the unchanged kernel', () => {
 const g=goal(), bad:Tree[]=[{leaf:[]},{leaf:[{kind:'input',index:-1}]},{leaf:[{kind:'input',index:1.5}]}]
 for(const t of bad){expect(check(g,t)).toBe(false);expect(slicedCheck(g,t,new Map())).toBe(false)}
 // Invalid unused products become zero rows in the existing kernel; preserve
 // that exact behavior rather than introducing a new pre-check refusal.
 for(const products of [[[0,9999]],[[-1,0]]] as [number,number][][]){const t={...proof(),products};expect(slicedCheck(g,t,new Map())).toBe(check(g,t))}
})
test('ordered paths, duplicates and changed truth values never share a leaf result', () => {
 const g:Goal={name:'paths',hyps:[atMost(x('a'),n(0))]},lin={a:1}
 const p:Path=new Map([[canon(lin),{lin,holds:false}]]), t:Tree={leaf:[{kind:'input',index:0},{kind:'input',index:1},{kind:'combine',a:0,b:1,ma:1,mb:1}]}
 for(const path of [p,new Map([[canon(lin),{lin,holds:true}]]),new Map([...p,['duplicate',{lin,holds:true}] as const])])expect(slicedCheck(g,t,path)).toBe(check(g,t,path))
})
test('slicing falls back rather than rejecting a needed implicit naturality row', () => {
 const g:Goal={name:'implicit row',hyps:[atMost(n(1),n(0)),atMost(x('extra'),n(9))]},p:Path=new Map(),rows=rowsAt(g,p)
 const nat=rows.findIndex(r=>canon(r.lin)===canon({extra:-1})), bad=rows.findIndex(r=>canon(r.lin)===canon({'1':1}))
 expect(nat).toBeGreaterThanOrEqual(0);expect(bad).toBeGreaterThanOrEqual(0)
 const t:Tree={products:[[nat,nat]],leaf:[{kind:'input',index:bad}]},before=conditionalProofStats()
 expect(check(g,t,p)).toBe(true);expect(slicedCheck(g,t,p)).toBe(true);expect(conditionalProofStats().leafFallbacks-before.leafFallbacks).toBe(1)
})
