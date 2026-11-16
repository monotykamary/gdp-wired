import {expect,test} from 'bun:test'
import {binder,encodeBinders,guardReserved,variable} from './dsl-binders.ts'
import {groupsOf} from './exists.ts'

test('integer existential aliases preserve legacy groups in either order',()=>{
  const root=binder('some',1)
  for(const some of [[root,`${root}$neg`],[`${root}$neg`,root]]){
    const encoded=encodeBinders({some,holds:{op:'=',a:variable(root),b:variable(`${root}$neg`)}},[])
    expect(groupsOf(encoded.some)).toEqual([['some$1','some$1$neg']])
    expect(encoded.holds.a.name).toBe('some$1')
    expect(encoded.holds.b.name).toBe('some$1$neg')
  }
})
test('only a colliding integer group renames and all its parts avoid free names',()=>{
  const one=binder('some',1),two=binder('some',2)
  const encoded=encodeBinders({some:[one,`${one}$neg`,two],free:variable('gdp$bound$2$neg'),holds:variable(`${one}$neg`)},['some$1','gdp$bound$1$neg'])
  expect(encoded.some).toEqual(['gdp$bound$3','gdp$bound$3$neg','some$2'])
  expect(encoded.holds.name).toBe('gdp$bound$3$neg')
  expect(encoded.free.name).toBe('gdp$bound$2$neg')
})
test('labels do not cause renaming and generated provenance is not a spelling guess',()=>{
  const key=binder('key',17)
  expect(encodeBinders({name:'key$17',forall:key,holds:variable(key)},[])).toEqual({name:'key$17',forall:'key$17',holds:{op:'var',name:'key$17'}})
  expect(()=>guardReserved(variable(key))).not.toThrow()
  expect(()=>guardReserved({op:'var',name:key})).toThrow('free reserved')
})
