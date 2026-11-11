import {expect,test} from 'bun:test'
import {type Goal,type Path,canon,check,framePath} from './kernel.ts'
import {clock} from './prove.ts'
import {growCdcl} from './cdcl.ts'

for(const holds of [true,false])test(`duplicate root aliases retain ${holds?'positive':'negative'} orientation`,()=>{
 const lin={rootX:1,'1':-1},root:Path=new Map([[canon(lin),{lin,holds}],['@0',{lin,holds}]])
 const goal:Goal={name:'duplicate root',hyps:[holds?{op:'<=',a:{op:'const',value:2},b:{op:'var',name:'rootX'}}:{op:'<=',a:{op:'var',name:'rootX'},b:{op:'const',value:1}}]}
 const before=JSON.stringify([...root]),q=growCdcl(goal,root,{nodes:0,until:clock()+100})
 expect(JSON.stringify([...root])).toBe(before)
 expect('tree'in q).toBe(true)
 if('tree'in q)expect(check(goal,q.tree,root)).toBe(true)
})

test('duplicate frame-cut rows remain checked at their original root',()=>{
 const frame={post:'post',pre:'pre',when:[]},root=framePath([frame,frame],[],new Map())
 expect([...root.keys()].some(k=>k.startsWith('@'))).toBe(true)
 const goal:Goal={name:'duplicate frame',hyps:[{op:'<',a:{op:'var',name:'pre'},b:{op:'var',name:'post'}}]}
 const q=growCdcl(goal,root,{nodes:0,until:clock()+100})
 expect('tree'in q).toBe(true)
 if('tree'in q)expect(check(goal,q.tree,root)).toBe(true)
})
