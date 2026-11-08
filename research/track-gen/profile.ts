// Production generators, unchanged allowances. Run in a fresh process on boat.
import {createHash} from 'node:crypto'
import {families,measure} from './meter.ts'
import {protocols} from '../protocols/ic3syn/models.ts'
import {candidates,guardLaws} from '../../core/counts.ts'
import {smallOf,trueSmall} from '../../core/exists.ts'
import {clock,counted,fullRate,withWall} from '../../kernel/prove.ts'
const start=performance.now(),protocol=protocols.find(p=>p.id==='mldr')!
const r=protocol.make(),m0=r.machine,caller=protocol.laws(r)
const result=withWall(start+60000,()=>{
 const g=measure('guard-laws',()=>guardLaws(m0)),m={...m0,counts:{...m0.counts,...g.counts}}
 families['guard-laws']!.laws.push(...g.laws)
 measure('small-warmup',()=>smallOf(m))
 return counted(fullRate,()=>{
  if(!caller.every(l=>trueSmall(m,[l])))throw new Error('invalid caller')
  const set=measure('generation',()=>candidates(m0,m,caller,caller,g.laws,60000,clock()+60000))
  const fingerprint=(x:unknown)=>createHash('sha256').update(JSON.stringify(x)).digest('hex')
  return {candidateCount:set.length,candidateHash:fingerprint(set),candidates:set,families:Object.fromEntries(Object.entries(families).map(([name,s])=>[name,{calls:s.calls,ms:s.ms,produced:s.laws.length,retained:set.filter(l=>s.laws.includes(l)).map(l=>l.name),laws:s.laws}])),wallMs:performance.now()-start}
 },true)
})
console.log(JSON.stringify(result))
