// One receipt per fresh process. No stale opaque-column registry or proof cache.
import {readFileSync} from 'node:fs'
import {type Goal,type LemmaCut,type Path,canon,check,lemmaPath,termColumn} from '../../kernel/kernel.ts'
import {brokenOf} from '../../kernel/prove.ts'
import {passesT10B} from './section10-ta-audit.ts'
import {supportsNamedGap,packetHash} from './section9-ta-audit.ts'
const file=process.argv[2];if(!file)throw new Error('receipt path required')
const r=JSON.parse(readFileSync(file,'utf8'))
const pathValid=(p:any[],m:Record<string,number>)=>p.every(([,a])=>{const n=Object.entries(a.lin).reduce((s,[k,v])=>s+Number(v)*(k==='1'?1:m[k]!),0);return Number.isFinite(n)&&(a.holds?n<=0:n>0)})
const model=(g:Goal,p:any[],m:Record<string,number>)=>brokenOf(g)(m).length===0&&pathValid(p,m)
if(r.side==='A'){
 const b=r.branches[0];if(!supportsNamedGap(b))throw new Error('control lost the gap')
 for(const a of b.attempts)if(!model(a.source,a.path,a.model))throw new Error('invalid control source model')
 for(const q of b.queries)if(!model(q.goal,q.path,q.model))throw new Error('invalid control numeric model')
 console.log(JSON.stringify({file,side:r.side,repeat:r.repeat,validatedSourceModels:b.attempts.length,validatedNumericModels:b.queries.length}));process.exit(0)
}
if(!passesT10B(r)||!r.pass)throw new Error('T-10A pass line failed')
if(!Array.isArray(r.columns)||!r.columns.length)throw new Error('term table missing')
for(const [i,e]of r.columns.entries())if(termColumn(e)!==`⟦${i}⟧`)throw new Error('term table identity mismatch')
if(r.originalPacketHash!==packetHash(r.oldPacket.g,r.oldPacket.cert,r.oldPacket.scope))throw new Error('original packet hash changed')
const c=r.packet,p:Path=new Map(c.path),a=r.attempt,n=r.numeric
if(c.cert.insts.length!==r.oldPacket.cert.insts.length+1||JSON.stringify(c.cert.insts.slice(0,-1))!==JSON.stringify(r.oldPacket.cert.insts))throw new Error('not exactly one appended instance')
if(!model(c.numeric,c.path,c.model))throw new Error('invalid captured selection model')
if(!check(a.proofSource,a.tree,p)||!check(n.goal,n.numericProof,p))throw new Error('source or numeric tree failed kernel replay')
const independent=(l:LemmaCut)=>{
 const goal={...c.g,hyps:l.slice?l.slice.map(i=>c.g.hyps[i]):c.g.hyps},path:Path=new Map();let duplicate=0
 for(const atom of [{lin:l.cut,holds:false},...l.when.map(lin=>({lin,holds:true}))]){const id=canon(atom.lin);path.set(path.has(id)?`@${duplicate++}`:id,atom)}
 return check(goal,l.tree,path)
}
if(!n.lemmas.every(independent))throw new Error('independent lemma replay failed')
if(!check(c.g,n.proof,lemmaPath(n.lemmas,p)))throw new Error('full conditional branch replay failed')
console.log(JSON.stringify({file,side:r.side,repeat:r.repeat,sourceTreeChecked:true,numericTreeChecked:true,independentLemmasChecked:n.lemmas.length,conditionalBranchChecked:true,sourceCore:a.coreSize,numericCore:r.numericCore,countedUnits:r.countedUnits}))
