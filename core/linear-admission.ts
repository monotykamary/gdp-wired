// Owned two-phase coefficient production. Discovery and output are DISTINCT
// physical cell operations; zero/cancelled inputs still cost discovery work.
// Domain: synchronous ordinary data records, no Proxy/exotic prototype. Native
// own-key enumeration still needs a candidate-specific M1/M3 summary; this
// module alone does not close the global SIZE/ORDER gate.
import {type Lin, add, scale, sub, v} from './solver.ts'
import {completeWorkProfile} from './work-profile.ts'
import {BudgetExpired, startWork, withAdmittedChunk} from './work-admission.ts'

type Input = Readonly<{lin: Lin, factor: number}>
function emitOwned(plan: Map<string, number>, keepZero: boolean, site: string): Lin {
  // The plan is local and owns primitive values, never references input cells.
  // Map.size and array.length below are intrinsic metadata of owned containers.
  const output: {key:string,value:number,charge:0|1}[] = [], iterator = plan.entries(), size = plan.size
  let nonzero=0
  for (let i = 0; i < size; i++) {
    startWork('tableCells', 1, `${site}:select`)
    const entry = iterator.next()
    if (entry.done) throw new Error('coefficient plan changed during selection')
    if(entry.value[1]!==0)nonzero++
    if (keepZero || entry.value[1] !== 0) output.push({key:entry.value[0],value:entry.value[1],charge:entry.value[1]===0?0:1})
  }
  return withAdmittedChunk('tableCells', nonzero, lease => {
    // This producer cannot return a partial row. Refuse before creating any
    // output coefficient, then let finally retire the unused reservation.
    if (lease.granted !== nonzero) throw new BudgetExpired(`${site}:emit`)
    const out: Lin = Object.create(null)
    for (let i = 0; i < output.length; i++) {
      const entry = output[i]!
      // Occupancy is cached metadata, not a repeated coefficient read. A zero
      // representation entry is no nonzero emission; start(0) validates life.
      lease.start(entry.charge)
      out[entry.key] = entry.value
    }
    return out
  }, `${site}:emit`)
}
function discover(inputs: readonly Input[], keepZero: boolean, site: string): Lin {
  const plan = new Map<string, number>()
  for (const {lin, factor} of inputs) {
    const prototype: unknown = Object.getPrototypeOf(lin)
    if (prototype !== null && prototype !== Object.prototype) throw new TypeError('coefficient input must be an ordinary data record')
    for (const key in lin) {
      startWork('tableCells', 1, `${site}:input`)
      const descriptor = Object.getOwnPropertyDescriptor(lin, key)
      if (!descriptor || !('value' in descriptor) || typeof descriptor.value !== 'number') throw new TypeError('coefficient input must have own numeric data cells')
      // This is the first cell lookup/arithmetic/accumulation, after start.
      const value: number = descriptor.value
      plan.set(key, plan.has(key) ? plan.get(key)! + value * factor : value * factor)
    }
  }
  return emitOwned(plan, keepZero, site)
}
export function fundedAdd(...inputs: Lin[]): Lin {
  if(!completeWorkProfile.enabled)return add(...inputs)
  const plan:Input[]=[]
  for(let i=0;i<inputs.length;i++){startWork('ticks',1,'linear add operand');plan.push({lin:inputs[i]!,factor:1})}
  return discover(plan,false,'linear:add')
}
export const fundedSub=(a:Lin,b:Lin):Lin=>admittedLinearSub(a,b,'linear:sub')
export const fundedScale=(a:Lin,factor:number):Lin=>admittedLinearScale(a,factor,'linear:scale')
export const fundedVariable=(name:string):Lin=>admittedLinearVariable(name,1,'linear:variable')
export function fundedConstant(value:number):Lin{
  if(!completeWorkProfile.enabled)return value===0?{}:{1:value}
  startWork('tableCells',1,'linear:constant:input')
  const plan=new Map<string,number>();if(value!==0)plan.set('1',value)
  return emitOwned(plan,false,'linear:constant')
}
export function admittedLinearProduct(a:Lin,b:Lin,keyOf:(p:string,q:string)=>string|undefined,site:string,safeIntegers:boolean):Lin|undefined{
  const plan=new Map<string,number>()
  for(const p in a)for(const q in b){
    startWork('tableCells',1,`${site}:left`)
    const ad=Object.getOwnPropertyDescriptor(a,p)
    if(!ad||!('value'in ad)||typeof ad.value!=='number')throw new TypeError('product input must have numeric data cells')
    const cp:number=ad.value
    startWork('tableCells',1,`${site}:right`)
    const bd=Object.getOwnPropertyDescriptor(b,q)
    if(!bd||!('value'in bd)||typeof bd.value!=='number')throw new TypeError('product input must have numeric data cells')
    const cq:number=bd.value,key=keyOf(p,q)
    if(key===undefined)return undefined
    const value=(plan.get(key)??0)+cp*cq
    if(safeIntegers&&![cp,cq,cp*cq,value].every(Number.isSafeInteger))return undefined
    plan.set(key,value)
  }
  return emitOwned(plan,false,site)
}
export function everyLinearCell(lin:Lin,test:(key:string,value:number)=>boolean,site:string):boolean{
  if(!completeWorkProfile.enabled)return Object.entries(lin).every(([key,value])=>test(key,value))
  for(const key in lin){
    if(completeWorkProfile.enabled)startWork('tableCells',1,site)
    const descriptor=Object.getOwnPropertyDescriptor(lin,key)
    if(!descriptor||!('value'in descriptor)||typeof descriptor.value!=='number')throw new TypeError('coefficient input must have numeric data cells')
    if(!test(key,descriptor.value))return false
  }
  return true
}
export function visitLinearCells(lin: Lin, visit: (key: string,value: number)=>void, site: string): void {
  if(!completeWorkProfile.enabled){for(const [key,value]of Object.entries(lin))visit(key,value);return}
  for(const key in lin){
    if(completeWorkProfile.enabled)startWork('tableCells',1,`${site}:visit`)
    const descriptor=Object.getOwnPropertyDescriptor(lin,key)
    if(!descriptor||!('value'in descriptor)||typeof descriptor.value!=='number')throw new TypeError('coefficient input must have numeric data cells')
    visit(key,descriptor.value)
  }
}
export function admittedLinearSub(a: Lin, b: Lin, site: string): Lin {
  return completeWorkProfile.enabled ? discover([{lin:a,factor:1},{lin:b,factor:-1}],false,site) : sub(a,b)
}
export function admittedLinearAdd(a: Lin, b: Lin, site: string): Lin {
  return completeWorkProfile.enabled ? discover([{lin:a,factor:1},{lin:b,factor:1}],false,site) : add(a,b)
}
export function admittedLinearScale(a: Lin, factor: number, site: string): Lin {
  return completeWorkProfile.enabled ? discover([{lin:a,factor}],false,site) : scale(a,factor)
}
export function admittedLinearCopy(a: Lin, site: string): Lin {
  return completeWorkProfile.enabled ? discover([{lin:a,factor:1}],true,site) : a
}
export function admittedLinearVariable(name: string, coefficient: number, site: string): Lin {
  if (!completeWorkProfile.enabled) return coefficient === 1 ? v(name) : {[name]:coefficient}
  startWork('tableCells',1,`${site}:construct`)
  const plan = new Map<string,number>();plan.set(name,coefficient)
  return emitOwned(plan,true,site)
}
