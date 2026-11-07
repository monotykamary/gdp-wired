import {expect,test} from 'bun:test'
import {type Machine,all,get,less,n,same,x} from '../../core/machine.ts'
import {canon} from '../../kernel/kernel.ts'
import {actionGuard,activeCarried} from './action-guard.ts'
const m:Machine={name:'two carried actions',params:[],inputs:['mode'],inputMaps:['Left','Right'],state:{},step:{flags:{eligible:{op:'all',key:'v',c:less(get('Right',x('v')),n(2))},first:same(x('mode'),n(2)),second:all(same(x('mode'),n(3)),{op:'flag',name:'eligible'})}}}
test('action guards use the selected operation and ground its quantified flag',()=>{
 expect(actionGuard(m,'mode',3)).toEqual(all(same(x('mode'),n(3)),same(x('?eligible'),n(1))))
 expect(actionGuard(m,'mode',9)).toBeUndefined()
})
test('the active quantified flag selects its carried set without protocol names',()=>{
 const lo={'?eligible':-1,'1':1},hi={'?eligible':1,'1':-1},path=new Map([[canon(lo),{lin:lo,holds:true}],[canon(hi),{lin:hi,holds:true}]])
 expect([...activeCarried(m,path)]).toEqual(['Right'])
 expect([...activeCarried(m,new Map())]).toEqual(['Left'])
})
