import {expect,test} from 'bun:test'
import {get,n,x,same,type E} from '../../core/machine.ts'
import {Meter} from './match.ts'
import {IteEGraph} from './ite.ts'
import {certify} from './certify.ts'
const ite=(v:E,a:E=n(1),b:E=n(2)):E=>({op:'if',c:{op:'<',a:v,b:n(3)},then:a,else:b})
test('ITE candidates decode to original terms and preserve guard and both branches',()=>{
  const g=new IteEGraph(new Meter(100000))
  const original=ite(x('actual'))
  g.seed([same(get('f',original),n(9))])
  expect(g.match([get('f',x('whole'))],['whole'])).toEqual([{whole:original}])
  expect(g.match([get('f',ite(x('guard')))],['guard'])).toEqual([{guard:x('actual')}])
  expect(g.match([get('f',ite(x('guard'),n(2),n(1)))],['guard'])).toEqual([])
  expect(g.match([get('f',{...original,op:'if',c:{op:'<=',a:x('guard'),b:n(3)}} as E)],['guard'])).toEqual([])
})
test('compound ITE guards roundtrip without Boolean or branch simplification',()=>{
  const original:E={op:'if',c:{op:'and',xs:[{op:'not',x:same(x('a'),n(2))},{op:'or',xs:[]}]},then:ite(x('a')),else:x('b')}
  const g=new IteEGraph(new Meter(100000));g.seed([same(get('f',original),n(8))])
  expect(g.match([get('f',x('whole'))],['whole'])).toEqual([{whole:original}])
})
test('ITE namespace collisions and quantified guards fail closed; encoding is metered',()=>{
  expect(()=>new IteEGraph(new Meter(100000)).seed([same(get('\u0000astra-ite:if',x('a')),n(0))])).toThrow('reserved')
  expect(()=>new IteEGraph(new Meter(1)).seed([same(ite(x('a')),n(0))])).toThrow('budget')
  expect(()=>new IteEGraph(new Meter(100000)).seed([same({op:'if',c:{op:'flag',name:'p'},then:n(1),else:n(2)},n(0))])).toThrow('unsupported ITE')
})
test('unchanged kernel replays both ITE branches, refusing a changed else branch',()=>{
  const base={name:'both ITE branches',hyps:[same(x('a'),x('b'))],rank:[n(0)],insts:[],uses:[]}
  const good=certify([],[{...base,concl:same(ite(x('c'),x('a'),n(0)),ite(x('c'),x('b'),n(0)))}])
  expect(good.checked).toBe(true)
  const bad=certify([],[{...base,concl:same(ite(x('c'),x('a'),n(0)),ite(x('c'),x('b'),n(1)))}])
  expect(bad.checked).toBe(false)
})
