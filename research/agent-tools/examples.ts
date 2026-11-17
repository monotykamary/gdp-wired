import type {Unit} from './protocol.ts'
import type {Law,E,C} from '../../core/machine.ts'
const v=(name:string):E=>({op:'var',name}),n=(value:number):E=>({op:'const',value})
const le=(a:E,b:E):C=>({op:'<=',a,b})
export function budget(broken=false):Unit {
  const increase:E={op:'add',a:v('spent'),b:v('cost')}
  const spent:E=broken?increase:{op:'min',a:v('cap'),b:increase}
  return {unit:'budget',rule:{name:'request budget',params:['cap'],inputs:['cost'],state:{spent:n(0)},step:{state:{spent}}}}
}
export const budgetLaws:Law[]=[{name:'spent never exceeds cap',holds:le(v('spent'),v('cap'))}]
export const budgetNearMiss:Law[]=[{name:'spent stays strictly below cap',holds:{op:'<',a:v('spent'),b:v('cap')}}]
export function permits(broken=false):Unit {
  const increase:E={op:'add',a:v('held'),b:n(1)}
  const acquire:E=broken?increase:{op:'min',a:v('capacity'),b:increase}
  const held:E={op:'if',c:{op:'=',a:v('acquire'),b:n(0)},then:{op:'sub',a:v('held'),b:n(1)},else:acquire}
  return {unit:'permits',rule:{name:'permit slots',params:['capacity'],inputs:['acquire'],state:{held:n(0)},assume:le(v('acquire'),n(1)),step:{state:{held}}}}
}
export const permitLaws:Law[]=[{name:'held never exceeds capacity',holds:le(v('held'),v('capacity'))}]
export const permitNearMiss:Law[]=[{name:'all slots always occupied',holds:{op:'=',a:v('held'),b:v('capacity')}}]
// Same conservation pattern as examples/infer.ts's connection pool, expressed as
// supported data. released <= acquired needs the inferred conservation helper.
export function permitAccounting():Unit {
  const got:C={op:'and',xs:[{op:'=',a:v('acquire'),b:n(1)},{op:'<',a:v('held'),b:v('capacity')}]}
  const back:C={op:'and',xs:[{op:'=',a:v('acquire'),b:n(0)},{op:'<',a:n(0),b:v('held')}]}
  const choose=(c:C,a:E,b:E):E=>({op:'if',c,then:a,else:b})
  const plus=(name:string):E=>({op:'add',a:v(name),b:n(1)})
  return {unit:'permits',rule:{name:'permit accounting',params:['capacity'],inputs:['acquire'],state:{held:n(0),acquired:n(0),released:n(0)},assume:le(v('acquire'),n(1)),step:{state:{held:choose(got,plus('held'),choose(back,{op:'sub',a:v('held'),b:n(1)},v('held'))),acquired:choose(got,plus('acquired'),v('acquired')),released:choose(back,plus('released'),v('released'))}}}}
}
export const permitAccountingLaws:Law[]=[{name:'released never exceeds acquired',holds:le(v('released'),v('acquired'))}]
