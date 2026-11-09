// Conditional research input: generated family plus the one explicitly supplied p1.
// This is not the original harness and cannot certify MLDR or an E-14 gate.
import {writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {protocols} from '../protocols/ic3syn/models.ts'
import {candidates,guardLaws} from '../../core/counts.ts'
import {smallOf,trueSmall} from '../../core/exists.ts'
import {clock,counted,fullRate,withWall} from '../../kernel/prove.ts'
import {type Law,type Machine,all,any,get,less,n,not,same,x} from '../../core/machine.ts'
const p=protocols.find(p=>p.id==='mldr')!,r=p.make(),caller=[...r.kindLaws(),...p.laws(r)],g=guardLaws(r.machine),m:Machine={...r.machine,counts:{...r.machine.counts,...g.counts}},support=new Set<Law>(),started=performance.now()
smallOf(m,r.machine)
const laws=withWall(performance.now()+60000,()=>counted(fullRate,()=>[...caller,...candidates(r.machine,m,caller,caller,g.laws,60000,clock()+60000,support)],true))
const row=Object.entries(m.counts??{}).find(([name,d])=>name.endsWith('$row')&&!d.lo)
if(!row)throw Error('no generated one-key row count')
const key='p1$research',a=x(key),p1:Law={name:'research Gp1: CV=0 implies empty row',forall:key,holds:any(not(all(less(a,x('size')),same(get('CV',a),n(0)))),same(get(row[0],a),n(0)))}
if(!trueSmall(m,[p1]))throw Error('p1 fails existing finite samples')
laws.push(p1)
const selectors={overlap:(s:string)=>s.includes('stored guard')&&s.endsWith('or disabled/0'),rows:(s:string)=>s.startsWith('fields:')&&s.includes('rows agree')&&s.includes('CV[')&&s.includes('CfgT[')&&!s.includes('CT['),star:(s:string)=>s.includes('no quorum canVote/3'),safety:(s:string)=>s==='one primary per term',p1:(s:string)=>s===p1.name}
const targets=Object.fromEntries(Object.entries(selectors).map(([tag,test])=>{const hits=laws.flatMap((l,i)=>test(l.name)?[i]:[]);if(hits.length!==1)throw Error(`${tag}: ${hits.length} matches; names=${laws.map(l=>l.name).join(';')}`);return[tag,hits[0]]}))
const payload={conditional:true,source:'current generated family plus explicitly supplied p1; finite Houdini not applied',m,laws,caller:caller.map(l=>laws.indexOf(l)),support:[...support].map(l=>laws.indexOf(l)),targets,generationWallMs:performance.now()-started},text=JSON.stringify(payload)
writeFileSync(process.argv[2]!,text)
console.log(JSON.stringify({phase:'family',conditional:true,laws:laws.length,targets:Object.fromEntries(Object.entries(targets).map(([k,i])=>[k,laws[i!]?.name])),generationWallMs:payload.generationWallMs,sha256:createHash('sha256').update(text).digest('hex')}))
