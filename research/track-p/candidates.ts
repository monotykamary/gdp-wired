import {readFileSync} from 'node:fs'
import {protocols} from '../protocols/ic3syn/models.ts'
import {candidates,guardLaws} from '../../core/counts.ts'
import {counted,clock,fullRate,withWall} from '../../kernel/prove.ts'
import {type Law} from '../../core/machine.ts'
const protocol=protocols.find(p=>p.id==='paxos_epr')!,r=protocol.make(),caller=[...r.kindLaws(),...protocol.laws(r)],g=guardLaws(r.machine),m={...r.machine,counts:{...r.machine.counts,...g.counts}}
const actual=withWall(performance.now()+60000,()=>counted(fullRate,()=>[...caller,...candidates(r.machine,m,caller,caller,g.laws,60000,clock()+60000)],true))
const reference=JSON.parse(readFileSync(process.argv[2]!,'utf8')) as {laws:Law[]}
const canonical=(l:Law)=>{const names=[l.forall,...(l.keys??[])].filter((n):n is string=>!!n),ks=new Map(names.map((n,i)=>[n,'B'+i])); const walk=(v:any):any=>Array.isArray(v)?v.map(walk):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).map(([k,x])=>[k,k==='name'&&typeof x==='string'?ks.get(x)??x:walk(x)])):v;return JSON.stringify(walk(l.holds))}
const indices=[2,3,4,7,9,10,11,13,14,17,33,45,61,64,66,70,71,73,74]
console.log(JSON.stringify({generated:actual.length,family:indices.map(i=>{const l=reference.laws[i]!,matched=actual.find(a=>canonical(a)===canonical(l));return {index:i,name:l.name,exact:actual.some(a=>a.name===l.name),alpha:matched?.name}})}))
console.log('CANDIDATES_BASE64',Buffer.from(JSON.stringify({machine:m,laws:actual})).toString('base64'))
