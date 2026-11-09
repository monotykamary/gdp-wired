// Separate counted goals. Only checked, empty-guard root lemmas are exported.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {type Goal,termColumn,columnTerm,mcGoal,countHyp,checkCounted,linear} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,grow,withWall} from '../../kernel/prove.ts'
import {sub} from '../../core/solver.ts'
import {countsForReads} from '../../core/count-facts.ts'
import {admitConditionalCut} from '../../core/count-recovery/conditional-cuts.ts'
const [input,candidates,out,budgetText='1000']=process.argv.slice(2);if(!input||!candidates||!out)throw new Error('PACKET CANDIDATES OUT [UNITS_PER_GOAL] required')
mkdirSync(out,{recursive:true});const p=JSON.parse(readFileSync(input,'utf8')),selection=JSON.parse(readFileSync(candidates,'utf8')),budget=Number(budgetText)
for(const [i,t]of p.columns.entries())if(termColumn(t)!==`⟦${i}⟧`)throw new Error('column restoration failed')
const root=mcGoal(p.packet.goal.hyps,p.packet.decls,p.cert),counts=countsForReads(p.packet.decls,p.cert.reads);if(!root||!counts)throw new Error('root construction failed')
const records:any[]=[],accepted:any[]=[],start=performance.now(),before=fullWork()
for(const index of selection.indices){
 const inst=p.cert.insts[index],hyp=countHyp(counts,inst);if(!hyp||hyp.op!=='or'||hyp.xs[0]?.op!=='<=')throw new Error('bad count identity '+index)
 const good=hyp.xs[0],a=linear(good.a,new Map()),b=linear(good.b,new Map());if(!a||!b)throw new Error('nonlinear cut')
 const cut=sub(a,b),goal:Goal={name:'state identity '+index,hyps:[{op:'not',x:good},hyp]},unitsBefore=fullWork(),wall=performance.now()
 const result=withWall(wall+30000,()=>counted(fullRate,()=>grow(goal,new Map(),{nodes:0,until:clock()+budget}),true))
 const checked='tree'in result&&checkCounted({name:goal.name,hyps:[{op:'not',x:good}],counts},{insts:[inst],tree:result.tree})
 const lemma=checked&&'tree'in result?admitConditionalCut(root,goal,result.tree,new Map(),new Map(),cut,[],performance.now()+10000):undefined
 const row={index,good,inst,checked,admitted:!!lemma,units:(fullWork()-unitsBefore)/fullRate,wallMs:performance.now()-wall,outcome:'tree'in result?'tree':result.stuck,why:'tree'in result?undefined:result.why,model:'tree'in result?undefined:result.witness,lemma:lemma??null}
 records.push(row);if(lemma){if(lemma.when.length)throw new Error('root fact acquired guards');accepted.push({index,good,lemma})}
 writeFileSync(join(out,'progress.json'),JSON.stringify({complete:records.length,accepted:accepted.length,units:(fullWork()-before)/fullRate})+'\n')
}
const columns=[];for(let i=0;;i++){const t=columnTerm(`⟦${i}⟧`);if(t===undefined)break;columns.push(t)}
const report={researchOnly:true,productionLocalDeadlines:true,budgetPerGoal:budget,requested:selection.indices,root,records,accepted,columns,units:(fullWork()-before)/fullRate,wallMs:performance.now()-start}
writeFileSync(join(out,'root-seeds.json'),JSON.stringify(report)+'\n');console.log(JSON.stringify({roots:{requested:records.length,checked:records.filter(r=>r.checked).length,admitted:accepted.length,units:report.units,wallMs:report.wallMs,results:records.map(({lemma:_lemma,...r})=>r)}}))
