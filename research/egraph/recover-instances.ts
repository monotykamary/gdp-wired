// Untrusted provenance recovery for EXISTING rows, not new assumptions or proofs.
import type {C,E,Law} from '../../core/machine.ts'
import {assumed,type Goal,type Instances} from '../../kernel/kernel.ts'
import {Exhausted,Meter} from './match.ts'
export function stableKey(o:unknown,meter:Meter):string{
  meter.tick()
  if(Array.isArray(o))return '['+o.map(v=>stableKey(v,meter)).join(',')+']'
  if(o&&typeof o==='object')return '{'+Object.keys(o).sort().map(k=>JSON.stringify(k)+':'+stableKey((o as Record<string,unknown>)[k],meter)).join(',')+'}'
  return JSON.stringify(o)??'undefined'
}
const expressionOps=new Set(['var','const','get','mul','proj','add','sub','min','max','prod','tup','if'])
export function recoverInstances(goal:Goal,laws:Law[],meter:Meter,maxRecords=512,progress={visitedRows:0,attemptedPairs:0,reconstructed:0}){
  if(!Number.isSafeInteger(maxRecords)||maxRecords<0)throw Error('invalid record cap')
  const instances:Instances={},records:{law:string,at:E[],path:number[]}[]=[],seen=new Set<string>()
  const unify=(p:unknown,t:unknown,names:Set<string>,env:Map<string,E>):boolean=>{
    meter.tick()
    if(p&&typeof p==='object'&&!Array.isArray(p)){
      const q=p as Record<string,unknown>
      if(q.op==='var'&&typeof q.name==='string'&&names.has(q.name)){
        if(!t||typeof t!=='object'||!expressionOps.has(String((t as Record<string,unknown>).op)))return false
        const old=env.get(q.name)
        if(old)return stableKey(old,meter)===stableKey(t,meter)
        env.set(q.name,t as E);return true
      }
    }
    if(Array.isArray(p))return Array.isArray(t)&&p.length===t.length&&p.every((v,i)=>unify(v,t[i],names,env))
    if(p&&typeof p==='object'){
      if(!t||typeof t!=='object'||Array.isArray(t))return false
      const keys=Object.keys(p),other=t as Record<string,unknown>
      return keys.length===Object.keys(t).length&&keys.every(k=>Object.hasOwn(other,k)&&unify((p as Record<string,unknown>)[k],other[k],names,env))
    }
    return p===t
  }
  const visit=(row:C,path:number[])=>{
    meter.tick();progress.visitedRows++
    for(const law of laws){
      meter.tick();progress.attemptedPairs++;if(!law.forall||law.holds.op!==row.op)continue
      const names=[law.forall,...law.keys??[]],env=new Map<string,E>()
      if(!unify(law.holds,row,new Set(names),env)||names.some(k=>!env.has(k)))continue
      const at=names.map(k=>env.get(k)!),identity=stableKey([law.name,at],meter)
      if(seen.has(identity))continue
      // Reconstruction by the existing kernel must reproduce the full original
      // row, including guards and both branches. Syntactic matching alone is not enough.
      stableKey(law.holds,meter)
      const generated=assumed([law],{[law.name]:at})
      if(generated.length!==1||stableKey(generated[0],meter)!==stableKey(row,meter))throw Error('kernel reconstruction mismatch')
      if(records.length>=maxRecords)throw new Exhausted('recovery record limit')
      seen.add(identity);instances[law.name]=[...(instances[law.name]??[]),...at];records.push({law:law.name,at,path});progress.reconstructed++
    }
    // Only positive conjuncts are existing assumptions; not disjuncts or negations.
    if(row.op==='and')row.xs.forEach((c,i)=>visit(c,[...path,i]))
  }
  goal.hyps.forEach((c,i)=>visit(c,[i]))
  return {instances,records}
}
