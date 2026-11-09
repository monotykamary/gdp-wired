// Checker-only replay of a direct legacy leaf. Not a whole-op or family gate.
import {readFileSync} from 'node:fs'
import {strict as assert} from 'node:assert'
import {canon,check,mcGoal,termColumn,type Path,type Goal} from '../../kernel/kernel.ts'
import {checkConditionalProof,markConditionalProof} from '../../core/count-recovery/conditional-proof.ts'
import {unpack} from './section18-codec.ts'
const x=unpack(readFileSync(process.argv[2]!,'utf8'))
assert.equal(x.record.legacyFixture,true);assert.equal(x.record.wholeOp,false)
assert.equal(x.record.allowance,6000);assert.equal(x.record.wallAllowance,7000)
for(const [i,t]of x.columns.entries())assert.equal(termColumn(t),`⟦${i}⟧`)
const root=mcGoal(x.packet.goal.hyps,x.packet.decls,x.cert);assert(root);assert.deepEqual(root.hyps,x.root.hyps)
for(const entry of x.seeds){const lemma=entry.lemma;assert(Array.isArray(lemma.slice)&&lemma.slice.every((i:number)=>Number.isInteger(i)&&i>=0&&i<root.hyps.length))
 const goal:Goal={name:root.name,hyps:lemma.slice.map((i:number)=>root.hyps[i]!)},against:Path=new Map([[canon(lemma.cut),{lin:lemma.cut,holds:false}]])
 assert.equal(lemma.when.length,0);assert(check(goal,lemma.tree,against))
}
for(const mark of x.marks){let tree=x.tree;for(const part of mark.path)tree=tree[part];markConditionalProof(mark.goal,tree,mark.lemmas)}
const checked=!!x.tree&&checkConditionalProof(root,x.tree,new Map(x.record.scope));assert.equal(checked,x.record.checked)
console.log(JSON.stringify({legacyFixture:true,wholeOp:false,op:x.record.op,checked,seedCount:x.seeds.length,units:x.record.units,wallMs:x.record.wallMs,searchError:x.record.searchError}))
