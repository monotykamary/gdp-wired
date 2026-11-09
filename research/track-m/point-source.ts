// Diagnostic only: rebuild the production cold packet and inspect one active
// setup row. This does not alter the production proof budget or its verdict.
import {readFileSync} from 'node:fs'
import {type Instances,canon,linear,mcGoal,countedObligations,check} from '../../kernel/kernel.ts'
import {type Machine,type Law,x,n,same,less} from '../../core/machine.ts'
import {clock,counted,fullRate,grow} from '../../kernel/prove.ts'
import {modelSequence} from '../../kernel/model-sequence.ts'
import {sub} from '../../core/solver.ts'
import {certFor} from '../../core/counts.ts'
import {countLawSeeds,countRowBridges,fieldGuardSeeds,fieldLawBridges,focusCountCert,rowKeyNames} from '../../core/count-focused.ts'
import {seedCountWitnessFlags} from '../../core/count-witness-flags.ts'
import {actionGuard} from '../../core/count-recovery/action-guard.ts'
import {fieldOnlyGoal} from '../../core/count-recovery/field-only.ts'
import {foldPath} from '../../core/count-recovery/fold-path.ts'
import {fieldCase} from '../../core/count-recovery/field-case.ts'
const [file,mode='0',relation='equal']=process.argv.slice(2),{m,laws}:{m:Machine,laws:Law[]}=JSON.parse(readFileSync(file!,'utf8')),value=Number(mode)
const index=laws.findIndex(l=>l.name.startsWith('Inv1758')),law=laws[index]!,names=[law.forall!,...law.keys??[]],own=names.map((v,i)=>x(i? v:`${v}#`)),scalar=rowKeyNames(m,law)
const rows=own.filter((_,i)=>scalar.has(names[i]!)),request=m.inputs.filter(name=>Object.values(m.counts??{}).some(d=>![d.j,d.lo,d.key].includes(name)&&JSON.stringify([d.below,d.body]).includes(`"name":${JSON.stringify(name)}`))).map(x)
let at:Instances=countLawSeeds(m,laws,{},rows,request,true,{requestDiagonals:true})
at=fieldLawBridges(m,laws,at,rows,request,own[2]);at[law.name]=[...at[law.name]??[],...own];at=countRowBridges(m,law,at,own,request);at=fieldGuardSeeds(m,at,[...rows,...request,n(0)])
const build=()=>{const packet=countedObligations(m,laws,{[law.name]:at},index).find(p=>p.goal.name.endsWith('@step'))!;return {...packet,cert:focusCountCert(m,packet.decls,certFor(packet.goal,packet.decls,true,1000),{structural:false,frames:true,algebraic:true,requestFrames:true,copyFrames:true,targets:rows})}}
let packet=build();at=seedCountWitnessFlags(m,at,[packet],true);packet=build()
const path=new Map(),hold=(c:any,yes=true)=>{if(c.op==='or'){hold(c.xs[0],yes);return}if(c.op==='and'){for(const p of c.xs)hold(p,yes);return}if(c.op==='not'){hold(c.x,!yes);return}if(c.op==='='){hold({op:'<=',a:c.a,b:c.b},yes);hold({op:'<=',a:c.b,b:c.a},yes);return}const a=linear(c.a,path),b=linear(c.b,path);if(!a||!b)throw new Error('nonlinear guard');const lin=sub(a,b);if(c.op==='<')lin['1']=(lin['1']??0)+1;path.set(canon(lin),{lin,holds:yes})}
for(let v=0;v<=6;v++)hold({op:'<=',a:x('op'),b:n(v)},v>=value)
hold(actionGuard(m,'op',value)!)
if(value===0){hold(same(own[0]!,n(0)));hold(less(n(0),own[1]!))}else{const writer=x(value===6?'j':'i');hold(same(own[0]!,writer));hold(relation==='above'?less(writer,own[1]!):relation==='below'?less(own[1]!,writer):same(own[1]!,writer))}
const original=mcGoal(packet.goal.hyps,packet.decls,packet.cert)!,field=fieldOnlyGoal(original,m,packet.cert,packet.goal.hyps.at(-1),path)
if(!field)throw new Error('expected a field projection')
const folded=foldPath(field,path),query=counted(fullRate,()=>modelSequence(path)(folded.goal,clock()+1000),true)
const out=counted(fullRate,()=>grow(folded.goal,path,{nodes:0,until:clock()+1000,units:true}),true)
const tree=counted(fullRate,()=>fieldCase(m,original,packet.cert,packet.goal.hyps.at(-1),path,clock()+1000),true),checked=!!tree&&check(original,tree,path)
console.log(JSON.stringify({value,relation,fieldProved:!!tree,checked,hyps:original.hyps.length,insts:packet.cert.insts.length,flags:Object.fromEntries(Object.entries(at).filter(([name])=>name.startsWith('?'))),query,grow:'tree'in out?'tree':out.stuck,core:query.core?.map(i=>folded.goal.hyps[i]),fieldGoal:folded.goal,path:[...path]}))
