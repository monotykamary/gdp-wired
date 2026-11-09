// Conditional Gp1 single-goal diagnostic, not an original-harness proof.
import {readFileSync} from 'node:fs'
import {countedAttempts} from '../../core/counts.ts'
import {type Law,type Machine,walkOnce} from '../../core/machine.ts'
import {mldrHandSet} from '../protocols/ic3syn/mldr2-probe.ts'
import {checkMC,countedObligations} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,withWall} from '../../kernel/prove.ts'
const [file,msArg='2700',supportArg='yes',repeat='1']=process.argv.slice(2),input=JSON.parse(readFileSync(file!,'utf8')),m:Machine=input.machine??input.m,laws:Law[]=[...input.laws],hand=process.env.MLDR_INCL_FAMILY!=='generated'
if(hand){const p1=mldrHandSet().laws.find(l=>l.name.startsWith('p1:'));if(!p1)throw Error('missing conditional init law');laws.push(p1)}
const law=laws.find(l=>l.name.startsWith('one primary'))!;if(!law)throw Error('missing safety')
const hasCount=(law:Law)=>{let found=false;walkOnce(law.holds,(o:any)=>{if(o.op==='get'&&Object.hasOwn(m.counts??{},o.map))found=true});return found}
const ms=Number(msArg),support=supportArg==='yes'?new Set(laws.filter(l=>input.support?input.support.includes(l.name):hasCount(l))):new Set<Law>(),start=performance.now(),work=fullWork()
const result=withWall(start+30000,()=>counted(fullRate,()=>{const attempts=countedAttempts(m,[law],support,clock()+ms);attempts.houdini=true;const out=attempts.traced(law,laws,1,ms),proof='proof'in out?out.proof:undefined;const checked=!!proof&&countedObligations(m,laws,{[law.name]:proof.instances},laws.indexOf(law)).every(o=>!!proof.certs[o.goal.name]&&checkMC(o.goal.hyps,o.decls,proof.certs[o.goal.name]!));return {proven:!!proof,checked,stuck:'stuck'in out?out.stuck:undefined,instances:proof?Object.fromEntries(Object.entries(proof.instances).map(([k,v])=>[k,v.length])):undefined}},true))
console.log(JSON.stringify({conditional:true,family:hand?'production-generated plus hand-supplied p1':'captured generated family (no hand law)',repeat,ms,support:supportArg,supportCount:support.size,law:law.name,laws:laws.length,...result,wallMs:performance.now()-start,countedMs:(fullWork()-work)/fullRate}))
