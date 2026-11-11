import {expect,test} from 'bun:test'
import {countRecipeGraph,type CountRecipeMember,type CountRecipeNode} from './count-recipe-graph.ts'
const known=(id:string,required:readonly string[]=[],terminal=false):CountRecipeNode=>({id,required,terminal})
const unknown=(id='ordinary',terminal=false):CountRecipeNode=>({id,terminal})
const member=(name:string,reference:number,recipes:readonly CountRecipeNode[]):CountRecipeMember=>({name,reference,recipes})
const ready=(name:string,reference:number,premises:readonly string[]=[],declared:readonly string[]=[],checkedReduced=true):CountRecipeMember=>({...member(name,reference,[known('done',declared,true)]),held:{premises,recipeId:'done',checkedReduced}})
const graph=(rows:readonly CountRecipeMember[],target='target')=>countRecipeGraph(rows,[target])
test('46.2: terminal half blocks every known path to target before another attempt',()=>{
 const rows=[member('half',27,[]),member('Inv',33,[known('lifted',['half'])]),member('K3',35,[known('row',['Inv'])]),member('target',99,[known('safety',['K3'])])]
 const result=graph(rows);expect(result.stop).toBe('target-blocked');expect(result.next).toBeUndefined();expect([...result.blocked]).toEqual(['half','Inv','K3','target'])
})
test('unknown-set alternative stays eligible when its known-set route is blocked',()=>{
 const result=graph([member('dead',0,[]),member('target',1,[known('strategy',['dead']),unknown()])]);expect(result.blocked.has('target')).toBe(false);expect(result.next?.recipe.id).toBe('ordinary')
})
test('unfinished nonterminal recipe does not enter Blocked',()=>{
 const result=graph([member('half',1,[known('lifted')]),member('target',2,[known('use',['half'])])]);expect(result.blocked.size).toBe(0);expect(result.next?.name).toBe('half')
})
test('only an accepted exact reduced scope overrides the producing declaration',()=>{
 const rows=[member('dead',0,[]),ready('target',1,[],['dead'],true)]
 expect(graph(rows).stop).toBe('nothing-eligible');expect(graph(rows).blocked.has('target')).toBe(false)
 const conservative=graph([rows[0]!,ready('target',1,[],['dead'],false)]);expect(conservative.stop).toBe('target-blocked');expect([...conservative.requirements.get('target')!]).toEqual(['dead'])
})
test('46.9: stranded held alternative runs once; completed producer never reopens',()=>{
 const producer=known('done',['dead'],true),alternative=unknown()
 const held:CountRecipeMember={name:'target',reference:1,recipes:[producer,alternative],held:{premises:['dead'],recipeId:'done',checkedReduced:false}}
 const rows=[member('dead',0,[]),held],first=graph(rows)
 expect(first.next?.recipe.id).toBe('ordinary');expect(first.next?.stranded).toBe(true)
 const failed=graph([rows[0]!,{...held,recipes:[producer,unknown('ordinary',true)]}]);expect(failed.stop).toBe('target-blocked');expect(failed.next).toBeUndefined()
 const replaced=graph([rows[0]!,{...held,recipes:[producer,unknown('ordinary',true)],held:{premises:[],recipeId:'ordinary',checkedReduced:true}}]);expect(replaced.stop).toBe('nothing-eligible');expect(replaced.usable.has('target')).toBe(true)
})
test('stranded held member with only an ineligible known alternative is blocked',()=>{
 const held:CountRecipeMember={...ready('target',1,['dead'],['dead'],false),recipes:[known('done',['dead'],true),known('other',['dead'])]}
 const result=graph([member('dead',0,[]),held]);expect(result.stop).toBe('target-blocked')
})
test('mutual known-set cycle stays unblocked and usable held cycle needs no attempt',()=>{
 const rows=[member('target',0,[known('a',['other'])]),member('other',1,[known('b',['target'])])],open=graph(rows)
 expect(open.blocked.size).toBe(0);expect(open.next?.name).toBe('target')
 const closed=graph([ready('target',0,['other']),ready('other',1,['target'])]);expect(closed.blocked.size).toBe(0);expect(closed.stop).toBe('nothing-eligible')
})
test('46.3: T301 cycle chooses half first regardless of supplied member order',()=>{
 const rows=[ready('base1',1),ready('base39',39),ready('base41',41),ready('base46',46),
  member('Inv',33,[known('lifted',['base1','half'])]),member('half',27,[known('lifted',['base1','Inv','K3','base39','base41','base46'])]),member('K3',35,[known('row',['Inv'])]),member('target',99,[known('safety',['Inv','half','K3'])])]
 for(const input of [rows,[...rows].reverse(),[...rows.slice(3),...rows.slice(0,3)]])expect(graph(input).next?.name).toBe('half')
})
test('a chain chooses the prerequisite, then its user after accepted scope changes',()=>{
 const a=member('target',0,[known('a',['b'])]),b=member('b',1,[known('b',['c'])]),c=member('c',2,[known('c')])
 expect(graph([a,b,c]).next?.name).toBe('c');expect(graph([a,b,ready('c',2)]).next?.name).toBe('b');expect(graph([a,ready('b',1,[]),ready('c',2)]).next?.name).toBe('target')
})
test('known recipe precedes unknown and exhausted instances never reappear under a new scope',()=>{
 const result=graph([member('target',0,[unknown(),known('known',[]),known('exhausted',[],true)])]);expect(result.next?.recipe.id).toBe('known')
 expect(()=>graph([member('target',0,[known('same'),known('same')])])).toThrow('duplicate recipe instance')
})
test('missing required laws block known routes rather than disappear',()=>{
 const result=graph([member('target',0,[known('known',['missing'])])]);expect(result.blocked.has('missing')).toBe(true);expect(result.stop).toBe('target-blocked')
})
