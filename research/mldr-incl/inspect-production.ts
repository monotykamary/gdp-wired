// Diagnostic replay of a production proposal, not a suite gate or acceptance tool.
import {readFileSync} from 'node:fs'
import {checkMC,countedObligations,mcGoal,type CountCert} from '../../kernel/kernel.ts'
import {usedHyps} from '../../kernel/prove.ts'
import {type Law,type Machine} from '../../core/machine.ts'
const p=JSON.parse(readFileSync(process.argv[2]!,'utf8')) as {machine:Machine,laws:Law[],law:string,proof:{instances:Record<string,any[]>,certs:Record<string,CountCert>}}
const index=p.laws.findIndex(l=>l.name===p.law);if(index<0)throw Error('law missing')
for(const o of countedObligations(p.machine,p.laws,{[p.law]:p.proof.instances},index)){
 const cert=p.proof.certs[o.goal.name];if(!cert||!checkMC(o.goal.hyps,o.decls,cert))throw Error('reconstructed production certificate rejected: '+o.goal.name)
 const g=mcGoal(o.goal.hyps,o.decls,cert)!;const used=usedHyps(g,cert.tree),base=g.hyps.length-cert.insts.length,reads=new Map(cert.reads.map(r=>[r[0],r.slice(1)]))
 const instances=cert.insts.flatMap((inst,j)=>used.has(base+j)?[{...inst,terms:inst.terms.map(([n,id])=>[n,reads.get(id)])}]:[])
 console.log(JSON.stringify({diagnostic:true,conditional:true,goal:o.goal.name,checked:true,laws:p.laws.length,rawPremises:o.goal.hyps.length,usedPremises:[...used].filter(j=>j<o.goal.hyps.length).sort((a,b)=>a-b),instances}))
}
