import {test,expect} from 'bun:test'
import {citations as c,liveInputs} from './section19-recorder.ts'
import {citationStage} from './section19-stage.ts'
test('nested source proofs are not all classified as the outer guard leaf',()=>{
 expect(citationStage({zones:['guard-leaf','closure-return','query'],attempt:3})).toBe('closure')
 expect(citationStage({zones:['guard-leaf','query'],attempt:3})).toBe('later-lemma')
 expect(citationStage({zones:['guard-leaf','query']})).toBe('leaf')
})
test('citation cone excludes unused inputs and zero-coefficient branches',()=>{
 expect(liveInputs([{kind:'input',index:3},{kind:'input',index:9},{kind:'combine',a:0,b:1,ma:1,mb:0}])).toEqual([3])
 expect(liveInputs([{kind:'input',index:8},{kind:'input',index:2},{kind:'cut',of:1,g:2}])).toEqual([2])
})
test('consumer provenance is frozen before later emissions',()=>{
 const good:any={op:'<=',a:{op:'var',name:'x'},b:{op:'const',value:3}},cut={x:1,'1':-3},g:any={name:'test',hyps:[good]},r:any={frames:[{id:0,name:'field'}],stack:[],phase:'initial'}
 c.reset(()=>r)
 c.call('before',g,new Map(),()=>{c.emission({id:1,meta:{good,helper:0}},{tree:{leaf:[]},cut});return {leaf:[]}})
 c.call('after',g,new Map([['cut',{lin:cut,holds:true}]]),()=>({leaf:[]}))
 expect(c.consumers[0].hypOwners).toEqual([])
 expect(c.consumers[1].hypOwners).toEqual([[0,[1]]])
 expect(c.consumers[1].pathOwners).toEqual([['cut',[1]]])
 const clone=c.transform('substC',(x:any)=>({...x}),[good]);expect(c.expressions.get(clone)).toEqual([1])
 c.enabled=false
})
test('only emitted trees get producer identities',()=>{
 const r:any={frames:[{name:'frame'}],stack:[]},good:any={op:'<=',a:{op:'const',value:0},b:{op:'const',value:1}}
 c.reset(()=>r);c.emission({id:4,meta:{good,helper:0}},{tree:undefined,cut:{'1':-1}})
 expect(c.emissions.length).toBe(0);c.enabled=false
})
