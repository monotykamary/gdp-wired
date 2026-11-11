import {expect,test} from 'bun:test'
import {countClosingNeeds} from './count-closing-needs.ts'
test('closing demand follows only reachable premises and terminates on self/cross cycles',()=>{
 const scopes=new Map([['caller',{premises:[{name:'invariant'}]}],['invariant',{premises:[{name:'invariant'},{name:'frame'}]}],['frame',{premises:[{name:'caller'}]}],['unused',{premises:[{name:'other'}]}]])
 expect([...countClosingNeeds(['caller'],scopes)]).toEqual(['caller','invariant','frame'])
})
test('missing proof demand is retained and all callers remain required',()=>{
 const scopes=new Map([['a',{premises:[{name:'missing'}]}]])
 expect([...countClosingNeeds(['a','b'],scopes)]).toEqual(['a','b','missing'])
 expect([...countClosingNeeds([],scopes)]).toEqual([])
})
