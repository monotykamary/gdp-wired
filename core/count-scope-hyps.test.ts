import {expect,test} from 'bun:test'
import {atMost,get,less,n,x} from './machine.ts'
import {type CountCert,type Count,type Goal,type Path,type Tree,canon,checkGoalLemmas,framePath,leafConstraints,linear} from '../kernel/kernel.ts'
import {countedCertificateHyps,replayCountCertificate} from './count-cert-transport.ts'
import {countedScopeHyps} from './count-scope-hyps.ts'
import {searchNow} from './wall.ts'

// A deliberately nonminimal certificate: M[i] < 0 is already contradictory,
// but this certificate proves it through M[j]'s naturality and an equal-key row.
// The fact M[j] <= 99 is never cited; it only makes the M[j] cell available.
// No search, re-solving, machine/law weakening or checker mock is used.
function fixture(options:{pair?:boolean,duplicate?:boolean,products?:boolean,frames?:boolean}={}){
 const mi=Object.keys(linear(get('M',x('i')),new Map())!)[0]!,mj=Object.keys(linear(get('M',x('j')),new Map())!)[0]!
 const goal:Goal={name:'pair-row source',hyps:[less(get('M',x('i')),n(0)),atMost(get('M',x('j')),n(99))]}
 if(options.duplicate)goal.hyps.push(atMost(get('M',x('j')),n(100)))
 const frames=options.frames?[{when:[],post:'post',pre:'pre'}]:[]
 const counts:Count[]=[{v:'post',key:'k',below:n(0),body:n(0)},{v:'pre',key:'k',below:n(0),body:n(0)}]
 const edge=(path:Path,split:Record<string,number>,holds:boolean)=>new Map(path).set(canon(split),{lin:split,holds})
 const make=(path:Path,pair:boolean):Tree=>{
  const rows=leafConstraints(goal,framePath(frames,[],path)),find=(fn:(r:typeof rows[number])=>boolean)=>{const i=rows.findIndex(fn);if(i<0)throw Error('fixture row missing');return i}
  const fact=find(r=>r.src!==undefined&&'fact'in r.src&&r.src.fact===0&&r.lin[mi]===1&&r.lin['1']===1)
  const nat=find(r=>r.src!==undefined&&'nat'in r.src&&r.src.nat===(pair?mj:mi))
  if(!pair)return {leaf:[{kind:'input',index:fact},{kind:'input',index:nat},{kind:'combine',a:0,b:1,ma:1,mb:1}]}
  const eq=find(r=>r.src!==undefined&&'pair'in r.src&&r.lin[mj]===1&&r.lin[mi]===-1)
  if(options.products){
   const base=rows.length,squares=[{[mi]:1}]
   return {squares,products:[[eq,eq],[base+1,base+1]],leaf:[{kind:'input',index:base+2},{kind:'input',index:fact},{kind:'input',index:eq},{kind:'combine',a:1,b:2,ma:1,mb:1},{kind:'input',index:nat},{kind:'combine',a:3,b:4,ma:1,mb:1}]}
  }
  return {leaf:[{kind:'input',index:fact},{kind:'input',index:eq},{kind:'combine',a:0,b:1,ma:1,mb:1},{kind:'input',index:nat},{kind:'combine',a:2,b:3,ma:1,mb:1}]}
 }
 const a={i:1,j:-1},b={j:1,i:-1},empty:Path=new Map(),yes=edge(empty,a,true)
 const tree:Tree={split:a,yes:{split:b,yes:make(edge(yes,b,true),options.pair!==false),no:make(edge(yes,b,false),false)},no:make(edge(empty,a,false),false)}
 const cert:CountCert={reads:[],insts:[],tree,...(frames.length?{frames}:{})}
 return {goal,cert,counts}
}
const sorted=(value:Set<number>|undefined)=>value&&[...value].sort((a,b)=>a-b)

test('used equal-key rows retain uncited cell suppliers as scope premises',()=>{
 const f=fixture()
 expect(checkGoalLemmas(f.goal,f.cert.tree,[],[],f.counts)).toBe(true)
 expect(sorted(countedCertificateHyps(f.goal,f.cert))).toEqual([0])
 expect(sorted(countedScopeHyps(f.goal,f.cert))).toEqual([0,1])
 const reduced={...f.goal,hyps:[f.goal.hyps[0]!]}
 expect(replayCountCertificate(f.goal,reduced,f.cert,searchNow()+30000)).toBeUndefined()
 const replayed=replayCountCertificate(f.goal,f.goal,f.cert,searchNow()+30000)
 expect(replayed).toBeDefined()
 if(replayed)expect(checkGoalLemmas(f.goal,replayed.tree,replayed.lemmas)).toBe(true)
})
test('a generated but unread pair does not retain its cell supplier',()=>{
 const f=fixture({pair:false})
 expect(checkGoalLemmas(f.goal,f.cert.tree,[],[],f.counts)).toBe(true)
 expect(sorted(countedScopeHyps(f.goal,f.cert))).toEqual([0])
})
test('every duplicate cell supplier is conservatively retained',()=>{
 const f=fixture({duplicate:true})
 expect(checkGoalLemmas(f.goal,f.cert.tree,[],[],f.counts)).toBe(true)
 expect(sorted(countedScopeHyps(f.goal,f.cert))).toEqual([0,1,2])
})
test('product dependencies and square offsets retain pair suppliers',()=>{
 const f=fixture({products:true})
 expect(checkGoalLemmas(f.goal,f.cert.tree,[],[],f.counts)).toBe(true)
 expect(sorted(countedScopeHyps(f.goal,f.cert))).toEqual([0,1])
})
test('native frame prefix is used rather than legacy unframed row indices',()=>{
 const f=fixture({frames:true})
 expect(checkGoalLemmas(f.goal,f.cert.tree,[],f.cert.frames,f.counts)).toBe(true)
 const old=countedCertificateHyps(f.goal,f.cert)!,next=countedScopeHyps(f.goal,f.cert)!
 expect([...old].every(i=>next.has(i))).toBe(true)
 expect(next.has(0)&&next.has(1)).toBe(true)
})
