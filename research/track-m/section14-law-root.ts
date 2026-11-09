// Resolve candidates not provable as unconditional count identities against the
// complete, unguarded law-root context. No leaf or op guard is supplied.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {termColumn,columnTerm,checkCounted,type Goal} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,grow,withWall} from '../../kernel/prove.ts'
import {countsForReads} from '../../core/count-facts.ts'
import {admitConditionalCut} from '../../core/count-recovery/conditional-cuts.ts'
const [packetFile,seedFile,out]=process.argv.slice(2);if(!packetFile||!seedFile||!out)throw new Error('PACKET SEEDS OUT required');mkdirSync(out,{recursive:true})
const p=JSON.parse(readFileSync(packetFile,'utf8')),seed=JSON.parse(readFileSync(seedFile,'utf8'))
for(const [i,t]of seed.columns.entries())if(termColumn(t)!==`⟦${i}⟧`)throw new Error('column restoration failed')
const counts=countsForReads(p.packet.decls,p.cert.reads);if(!counts)throw new Error('count declarations missing')
const raw=seed.root.hyps.slice(0,-p.cert.insts.length),insts=seed.root.hyps.slice(-p.cert.insts.length),records:any[]=[],accepted=[...seed.accepted],start=performance.now(),before=fullWork()
for(const old of seed.records.filter((r:any)=>!r.admitted)){
 const base=[...raw,{op:'not' as const,x:old.good}],goal:Goal={name:'law-root consequence '+old.index,hyps:[...base,...insts]},t=performance.now(),w=fullWork()
 const q=withWall(t+30000,()=>counted(fullRate,()=>grow(goal,new Map(),{nodes:0,until:clock()+1000}),true)),checked='tree'in q&&checkCounted({name:goal.name,hyps:base,counts},{insts:p.cert.insts,tree:q.tree})
 const cut=Object.fromEntries(old.inst.terms.map(([k,v]:[number,string])=>[v,k]));if(old.inst.unit)cut.size=old.inst.unit
 const lemma=checked&&'tree'in q?admitConditionalCut(seed.root,goal,q.tree,new Map(),new Map(),cut,[],performance.now()+10000):undefined
 const row={index:old.index,checked,admitted:!!lemma,units:(fullWork()-w)/fullRate,wallMs:performance.now()-t,outcome:'tree'in q?'tree':q.stuck,why:'tree'in q?undefined:q.why,model:'tree'in q?undefined:q.witness}
 records.push(row);if(lemma){if(lemma.when.length)throw new Error('unexpected guard');accepted.push({index:old.index,good:old.good,lemma})}
 writeFileSync(join(out,'progress.json'),JSON.stringify({complete:records.length,accepted:accepted.length,units:(fullWork()-before)/fullRate})+'\n')
}
const columns=[];for(let i=0;;i++){const t=columnTerm(`⟦${i}⟧`);if(t===undefined)break;columns.push(t)}
const result={...seed,accepted,columns,lawRoot:{noOpGuard:true,noLeafGuard:true,budgetPerGoal:1000,units:(fullWork()-before)/fullRate,wallMs:performance.now()-start,records},totalUnits:seed.units+(fullWork()-before)/fullRate}
writeFileSync(join(out,'root-seeds.json'),JSON.stringify(result)+'\n');console.log(JSON.stringify({lawRoot:{accepted:accepted.length,additional:accepted.length-seed.accepted.length,units:result.lawRoot.units,wallMs:result.lawRoot.wallMs,records}}))
