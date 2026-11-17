// Diagnostic only: copies the checker replay to explain the first rejected step.
// It does not replace or alter the actual checker used to accept a proof.
import {writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {fixedInt, rule} from '../../core/dsl.ts'
import {proveStepLaws} from '../../kernel/prove.ts'
import {canon, check, checkLaws, leafConstraints, obligations, stepLawObligations, withProducts, type Goal, type Path, type Tree} from '../../kernel/kernel.ts'
import type {Constraint, Lin, Step} from '../../core/solver.ts'
const output = process.env.SUPERCOMPUTER_OUTPUT_DIR
if (!output) throw Error('results-only diagnostic requires output directory')
const save = (name: string, data: unknown) => writeFileSync(join(output, name), JSON.stringify(data) + '\n')
const exact = (r: Lin) => Object.values(r).every(Number.isSafeInteger)
function replay(cs: Constraint[], steps: Step[]): unknown {
 const rows: Lin[] = []
 for (const [i,s] of steps.entries()) {
  if (s.kind === 'input') {
   if (!Number.isInteger(s.index) || s.index<0 || s.index>=cs.length) return {i,reason:'input-index',step:s,count:cs.length}
   const r=cs[s.index]!.lin
   if (!exact(r)) return {i,reason:'unsafe-input',step:s,row:r}
   rows.push(r)
  } else if (s.kind === 'combine') {
   if (!(s.a<i && s.b<i && Number.isSafeInteger(s.ma) && Number.isSafeInteger(s.mb) && s.ma>0 && s.mb>0)) return {i,reason:'combine-parameters',step:s}
   const out:Lin=Object.create(null)
   for (const [r,m] of [[rows[s.a]!,s.ma],[rows[s.b]!,s.mb]] as const) for (const [key,c] of Object.entries(r)) {
    if (!Number.isSafeInteger(m*c)) return {i,reason:'unsafe-product',step:s,key,coefficient:c,multiplier:m,product:String(m*c),a:rows[s.a],b:rows[s.b]}
    out[key]=(out[key]??0)+m*c
   }
   if (!exact(out)) return {i,reason:'unsafe-sum',step:s,row:out}
   rows.push(out)
  } else {
   const r=rows[s.of], keys=r?Object.keys(r).filter(k=>k!=='1'):[]
   if (!(r && s.of<i && Number.isSafeInteger(s.g) && s.g>0 && keys.every(k=>r[k]!%s.g===0))) return {i,reason:'cut',step:s,row:r}
   rows.push({...Object.fromEntries(keys.map(k=>[k,r[k]!/s.g])),1:Math.ceil((r['1']??0)/s.g)})
  }
 }
 const last=rows.at(-1)
 return {reason:'final-row',last,positive:!!last&&(last['1']??0)>0,variablesZero:!!last&&Object.keys(last).filter(k=>k!=='1').every(k=>last[k]===0)}
}
function rejected(goal:Goal,tree:Tree,path:Path=new Map(),route=''):unknown {
 if ('leaf' in tree) {
  const raw=leafConstraints(goal,path), rows=withProducts(raw,tree.products??[],tree.squares)
  save('failing-leaf.json',{goal,path:[...path],route,raw,rows,tree})
  return {goal:goal.name,route,pathDepth:path.size,rows:rows.length,steps:tree.leaf.length,rejection:replay(rows,tree.leaf)}
 }
 const id=canon(tree.split)
 if(path.has(id)||Object.keys(tree.split).every(k=>k==='1'))return{goal:goal.name,route,reason:'invalid-split',split:tree.split}
 const yes=new Map(path).set(id,{lin:tree.split,holds:true}),no=new Map(path).set(id,{lin:tree.split,holds:false})
 return !check(goal,tree.yes,yes)?rejected(goal,tree.yes,yes,route+'Y'):rejected(goal,tree.no,no,route+'N')
}
const k=fixedInt(64,false)
const r=rule('u64 diagnostic').inputs({n:k,d:k}).state({q:k.from('0'),rem:k.from('0')})
 .step(({n,d})=>({q:n.div(d,'FLOOR','TRAP'),rem:n.rem(d,'FLOOR','TRAP')}))
const sl=r.stepLaw('identity',(before,after)=>before.d.eq(k.lift(0n)).not().implies(after.q.mul(before.d,'WRAP').plus(after.rem,'WRAP').eq(before.n)))
const m=r.machine,laws=r.kindLaws(),start=performance.now(),report=proveStepLaws(m,laws,[sl])
console.log(JSON.stringify({proven:report.proven,checked:report.checked,ms:performance.now()-start,nodes:report.nodes,leaves:report.leaves}))
if(!report.proof)throw Error('no candidate proof')
save('candidate.json',{machine:m,laws,stepLaws:[sl],proof:report.proof})
const baseOK=checkLaws(m,laws,report.proof.laws)
console.log(JSON.stringify({baseOK}))
const goals=baseOK?stepLawObligations(m,laws,report.proof.perStep?.[sl.name]??report.proof.instances,sl):obligations(m,laws,report.proof.laws.instances)
const trees=baseOK?report.proof.trees:report.proof.laws.trees
for(const g of goals){const t=trees[g.name];const ok=!!t&&check(g,t);console.log(JSON.stringify({goal:g.name,ok}));if(t&&!ok){const reason=rejected(g,t);save('rejection.json',reason);console.log(JSON.stringify(reason));break}}
