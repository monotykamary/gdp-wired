import {expect,test} from 'bun:test'
import {atMost,less,minus,n,plus,times,x} from '../machine.ts'
import {sub} from '../solver.ts'
import {canon,check,linear,type Path} from '../../kernel/kernel.ts'
import {clock} from '../../kernel/prove.ts'
import {naturalSplits,proveNaturalCases} from './natural-cases.ts'

function fixture(union=true){
 const dx=x('xOnly'),dy=x('sOnly'),both=x('both'),hx=x('hx'),hy=x('hy'),bad=x('bad'),quorum=x('quorum'),xs=plus(dx,both),ss=plus(dy,both)
 const overlap=plus(minus(plus(hx,n(1)),dx),minus(plus(hy,n(1)),dy)),lin=sub(linear(plus(both,n(1)),new Map())!,linear(overlap,new Map())!)
 const root:Path=new Map([[canon(lin),{lin,holds:true}]])
 const hyps=[...[dx,dy,both,hx,hy,bad,quorum].map(v=>atMost(n(0),v)),atMost(times(2,hx),xs),less(xs,plus(times(2,hx),n(2))),atMost(times(2,hy),ss),less(ss,plus(times(2,hy),n(2))),less(xs,times(2,quorum)),less(ss,times(2,bad)),atMost(quorum,xs),atMost(bad,ss),less(both,overlap),...(union?[atMost(plus(bad,quorum),plus(dx,plus(dy,both)))]:[])]
 return {g:{name:'natural overlap',hyps},root}
}

test('natural subtraction cases recover a checked overlap contradiction under its guard path',()=>{
 const {g,root}=fixture(),trace:object[]=[]
 expect(naturalSplits(g,root)).toHaveLength(2)
 const tree=proveNaturalCases(g,root,clock()+1000,trace)
 if(!tree)console.error(JSON.stringify({naturalTrace:trace}))
 expect(tree).toBeDefined();if(tree)expect(check(g,tree,root)).toBe(true)
})

test('natural subtraction cases cannot invent the missing union bound',()=>{
 const {g,root}=fixture(false)
 expect(proveNaturalCases(g,root,clock()+1000)).toBeUndefined()
})
