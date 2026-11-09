import {expect,test} from 'bun:test'
import {get,ite,less,n,same,x} from '../../core/machine.ts'
import {fieldCountDemand} from './field-count-demand.ts'
function fixture(){
 const d={j:'row',key:'k',below:n(4)},ds=[{...d,map:'Bounded',body:ite(less(get('Value',x('k')),get('Limit',n(0))),n(1),n(0))},{...d,map:'Carried',body:get('Parcel',x('k'))}]
 const cert={reads:[['bounded','Bounded',n(0)],['carried','Carried',n(0)]] as [string,string,ReturnType<typeof n>][],insts:[{wit:'w',below:n(4),unit:0,terms:[[1,'carried'],[-1,'bounded']] as [number,string][]}]}
 return {ds,cert,claim:same(get('Limit',n(0)),n(2))}
}
test('a scalar field selects its declared count dependency and existing coupled read without mutation',()=>{
 const f=fixture(),before=JSON.stringify(f)
 expect([...fieldCountDemand(f.ds,f.cert,f.claim)]).toEqual(['bounded','carried'])
 expect(JSON.stringify(f)).toBe(before)
})
test('different cells and unrelated maps do not create count demand',()=>{
 const f=fixture()
 expect(fieldCountDemand(f.ds,f.cert,same(get('Limit',n(1)),n(2))).size).toBe(0)
 expect(fieldCountDemand(f.ds,f.cert,same(get('Other',n(0)),n(2))).size).toBe(0)
})
test('no claim, exhausted cap, and count-only claims keep the old path',()=>{
 const f=fixture()
 expect(fieldCountDemand(f.ds,f.cert,undefined).size).toBe(0)
 expect(fieldCountDemand(f.ds,f.cert,f.claim,0).size).toBe(0)
 expect(fieldCountDemand(f.ds,f.cert,same(get('Bounded',n(0)),n(0))).size).toBe(0)
 expect([...fieldCountDemand(f.ds,f.cert,f.claim,1)]).toEqual(['bounded'])
})
test('a cyclic claim is refused',()=>{
 const f=fixture(),bad:any={op:'not'};bad.x=bad
 expect(fieldCountDemand(f.ds,f.cert,bad).size).toBe(0)
})
