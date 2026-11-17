import {expect, test} from 'bun:test'
import {fixedInt, proveSteps, rule} from './dsl.ts'
import {wordDivisionFacts, wordDivisionKey, wordDivisionName} from '../kernel/word-division.ts'
import {evalC, interpret, loadJs, type E} from './machine.ts'

test('u64 word quotient identity checks without unsafe upper-carry elimination', () => {
  const k = fixedInt(64, false)
  const r = rule('u64 quotient identity').inputs({n:k,d:k}).state({q:k.from('0'),rem:k.from('0')})
    .step(({n,d}) => ({q:n.div(d,'FLOOR','TRAP'),rem:n.rem(d,'FLOOR','TRAP')}))
  const identity = r.stepLaw('word identity', (before,after) => before.d.eq(k.lift(0n)).not().implies(
    after.q.mul(before.d,'WRAP').plus(after.rem,'WRAP').eq(before.n)))
  const v = proveSteps(r, [], [identity], {search:false,watchdogMs:30_000})
  expect(v.proven).toBe(true); expect(v.checked).toBe(true)
  const max=(1n<<64n)-1n
  for(const engine of [interpret(r.machine),loadJs(r.machine)])
    for(const a of [0n,1n,max-1n,max])for(const b of [1n,2n,3n,max]){
      const after=engine.step({},engine.init({}),{...k.encode('n',a.toString()),...k.encode('d',b.toString())})
      const q=BigInt(k.decode('q',after.scalars) as string|number),rem=BigInt(k.decode('rem',after.scalars) as string|number)
      expect(q).toBe(a/b);expect(rem).toBe(a%b);expect(q*b+rem).toBe(a)
    }
}, 60_000)

test('local carry cuts do not certify a shifted false word identity', () => {
  const k = fixedInt(64,false)
  const r = rule('false u64 identity').inputs({n:k,d:k}).state({q:k.from('0'),rem:k.from('0')})
    .step(({n,d})=>({q:n.div(d,'FLOOR','TRAP'),rem:n.rem(d,'FLOOR','TRAP')}))
  const wrong = r.stepLaw('shifted identity',(before,after)=>before.d.eq(k.lift(0n)).not().implies(
    after.q.mul(before.d,'WRAP').plus(after.rem,'WRAP').eq(before.n.plus(k.lift(1n),'WRAP'))))
  // For n=7,d=3 the actual quotient/remainder are2,1: the left side is7, not8.
  const v = proveSteps(r,[],[wrong],{search:false,watchdogMs:10_000})
  expect(v.proven).toBe(false)
  expect(v.kernelProven).not.toBe(true)
},30_000)

test('carry after the low word is zero for boundary quotients at all widths', () => {
  for (const width of [8,16,32,64] as const) {
    const n = width===8?1:width/16, base = width===8?256n:65536n, max=(1n<<BigInt(width))-1n
    for (const a of [0n,1n,max-1n,max]) for (const b of [1n,2n,3n,max]) {
      const values=[a,b].flatMap(x=>Array.from({length:n},(_,i)=>Number(x/base**BigInt(i)%base)))
      const key=wordDivisionKey(values.map(value=>({op:'const',value} as E)))
      const clauses=wordDivisionFacts([{op:'get',map:wordDivisionName(width,'q',0),key}])
      for(const clause of clauses)expect(evalC(clause,{}, {scalars:{},maps:{}}, {name:'boundary',params:[],inputs:[],state:{},step:{}})).toBe(true)
    }
  }
})
