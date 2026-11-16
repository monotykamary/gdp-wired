import {expect,test} from 'bun:test'
import {encodeBinders} from './dsl-binders.ts'
import {groupsOf} from './exists.ts'

test('integer existential aliases preserve a group in either order',()=>{
  for(const some of [['?some1','?some1$neg'],['?some1$neg','?some1']]){
    const encoded=encodeBinders({some,holds:{op:'=',a:{op:'var',name:'?some1'},b:{op:'var',name:'?some1$neg'}}},[])
    const groups=groupsOf(encoded.some)
    expect(groups).toHaveLength(1)
    expect(groups[0]).toHaveLength(2)
    expect(groups[0]![1]).toBe(`${groups[0]![0]}$neg`)
    expect(encoded.holds.a.name).toBe(groups[0]![0])
    expect(encoded.holds.b.name).toBe(groups[0]![1])
  }
})
test('an entire integer alias group avoids declared and later free names',()=>{
  const encoded=encodeBinders({some:['?some1','?some1$neg','?some2'],free:'gdp$bound$2$neg',holds:{op:'var',name:'?some1$neg'}},['gdp$bound$1$neg'])
  expect(encoded.some).toEqual(['gdp$bound$3','gdp$bound$3$neg','gdp$bound$4'])
  expect(encoded.holds.name).toBe('gdp$bound$3$neg')
  expect(encoded.free).toBe('gdp$bound$2$neg')
})
