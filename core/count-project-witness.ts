// A deliberately weaker member query, never an accepted proof by itself.
// Keep pointwise-map premises only at the selected CountInst witnesses. Scalar
// endpoint guards stay available; the caller must rebase/check the full goal.
import {type C,walkOnce} from './machine.ts'
import {type Count,type CountInst,type Path,canon} from '../kernel/kernel.ts'
// Keep the selected witness's activating comparison, but not unrelated count
// comparisons already accumulated by earlier transports. Rebase to the full
// root before accepting any returned tree.
export function projectCountWitnessRoot(path:Path,counts:Count[],selected:CountInst[]):Path{
 const names=new Set(counts.map(count=>count.v)),active=new Set(selected.map(inst=>{
  const row:Record<string,number>={}
  for(const [coefficient,id]of inst.terms)row[id]=(row[id]??0)+coefficient
  if(inst.unit)row['1']=-inst.unit
  return canon(row)
 }))
 return new Map([...path].filter(([,atom])=>active.has(canon(atom.lin))||!Object.keys(atom.lin).some(name=>names.has(name))))
}
export function projectCountWitness(hyps:C[],counts:Count[],selected:CountInst[]):C[]{
 const ids=new Set(selected.flatMap(inst=>inst.terms.map(([,id])=>id))),maps=new Set<string>(),endpoints=new Set<string>(),witnesses=new Set(selected.map(inst=>inst.wit))
 for(const count of counts)if(ids.has(count.v))walkOnce(count.body,(node:any)=>{
  if(node.op==='var'&&node.name!==count.key)endpoints.add(node.name)
  if(node.op!=='get')return
  let member=false;walkOnce(node.key,(key:any)=>{if(key.op==='var'&&key.name===count.key)member=true})
  if(member)maps.add(node.map)
 })
 return hyps.filter(hyp=>{
  let pointwise=false,member=false,endpointOnly=true
  walkOnce(hyp,(node:any)=>{
   if(node.op==='get'&&maps.has(node.map)){pointwise=true;walkOnce(node.key,(key:any)=>{if(key.op==='var'&&!endpoints.has(key.name))endpointOnly=false})}
   if(node.op==='var'&&witnesses.has(node.name))member=true
  })
  return !pointwise||member||endpointOnly
 })
}
