import {expect, test} from 'bun:test'
import {inferLaws} from './infer.ts'
import {type Machine, type Law, all, atMost, get, ite, less, n, not, plus, same, x} from './machine.ts'

test('cube-only requests do not build wider cubes before filtering them out', () => {
  // Each cell triple has even parity. Every two-literal combination occurs, but
  // odd-parity three-literal cubes are absent: a width-two caller needs none.
  const m: Machine = {name:'even cell triples',params:['N'],inputs:['i','kind'],state:{},maps:{A:0,B:0,C:0},
    assume:all(less(x('i'),x('N')),less(x('kind'),n(3))),
    step:{maps:{
      A:{key:x('i'),value:ite(less(x('kind'),n(2)),n(1),n(0))},
      B:{key:x('i'),value:ite(not(same(x('kind'),n(1))),n(1),n(0))},
      C:{key:x('i'),value:ite(not(same(x('kind'),n(0))),n(1),n(0))},
    }}}
  const law: Law = {name:'at most two',keys:['k'],holds:atMost(plus(plus(get('A',x('k')),get('B',x('k'))),get('C',x('k'))),n(2))}
  const run = (cubes: number) => {
    let made = 0
    const out = inferLaws(m,[law],[],{cubes,ms:10000,progress:(phase,info)=>{if(phase==='join pool')made+=Number(info.made)}})
    return {made,found:out.found}
  }
  const narrow=run(2),wide=run(3)
  expect(wide.found.length).toBeGreaterThan(0)
  expect(narrow.found).toEqual([])
  expect(narrow.made).toBeLessThan(wide.made)
},60000)
