import {expect,test} from 'bun:test'
import {countRecipeGraph,type CountRecipeMember} from './count-recipe-graph.ts'
const row=(name:string,reference:number,required:readonly string[]|undefined,terminal=false):CountRecipeMember=>({name,reference,recipes:[{id:'recipe',required,terminal}]})
const run=(rows:readonly CountRecipeMember[])=>countRecipeGraph(rows,['target'])
test('46.15 unknown target considers the fixed inventory without inventing edges',()=>{
 const result=run([row('target',9,undefined),row('base',1,[])])
 expect([...result.closure]).toEqual(['target']);expect([...result.candidates]).toEqual(['target','base'])
 expect([...result.requirements.get('target')!]).toEqual([]);expect(result.next?.name).toBe('base')
})
test('46.15 unknown member of known closure also widens consideration',()=>{
 const result=run([row('target',9,['dependency']),row('dependency',8,undefined),row('base',1,[])])
 expect([...result.closure]).toEqual(['target','dependency']);expect(result.candidates.has('base')).toBe(true)
 expect([...result.requirements.get('dependency')!]).toEqual([])
})
test('46.15 known empty, terminal unknown and usable unknown never trigger expansion',()=>{
 const outside=row('outside',0,[])
 expect(run([row('target',9,[]),outside]).candidates.has('outside')).toBe(false)
 expect(run([row('target',9,undefined,true),outside]).candidates.has('outside')).toBe(false)
 const held={...row('target',9,undefined,true),held:{premises:[],recipeId:'recipe',checkedReduced:true}}
 expect(run([held,outside]).candidates.has('outside')).toBe(false)
})
test('46.15 scores the expanded domain using only real known edges',()=>{
 const rows=[row('target',9,undefined),row('dependency',7,[]),row('user',1,['dependency'])]
 for(const order of [rows,[...rows].reverse(),[rows[1]!,rows[0]!,rows[2]!]]){
  const result=run(order);expect(result.next?.name).toBe('dependency');expect(result.next?.weight).toBe(1)
  expect([...result.requirements.get('target')!]).toEqual([])
 }
})
test('46.15 blocked candidates remain unstartable; consuming the trigger shrinks the domain',()=>{
 const outside=row('outside',0,['missing']),trigger=row('target',9,undefined)
 expect(run([trigger,outside]).next?.name).toBe('target')
 const consumed={...trigger,recipes:[{id:'recipe',terminal:true},{id:'known',required:[],terminal:false}]}
 const next=run([consumed,row('eligible-outside',1,[])])
 expect([...next.candidates]).toEqual(['target']);expect(next.next?.recipe.id).toBe('known')
})
test('F5 only an explicitly checked external basis discharges a missing member',()=>{
 const rows=[row('target',9,['basis'])]
 expect(run(rows).stop).toBe('target-blocked')
 const result=countRecipeGraph(rows,['target'],()=>{}, {basis:new Set(['basis'])})
 expect(result.blocked.has('basis')).toBe(false);expect(result.next?.name).toBe('target')
 expect([...result.requirements.get('target')!]).toEqual(['basis'])
})
test('46.15 an unknown target route survives a failed half, but known-only inventory blocks',()=>{
 const half=row('half',1,[],true),known={id:'known',required:['half'],terminal:false}
 const open=run([half,{name:'target',reference:9,recipes:[known,{id:'ordinary',terminal:false}]}])
 expect(open.blocked.has('target')).toBe(false);expect(open.next?.recipe.id).toBe('ordinary')
 const blocked=run([half,{name:'target',reference:9,recipes:[known]}])
 expect(blocked.stop).toBe('target-blocked');expect(blocked.next).toBeUndefined()
})
