// Synthetic runtime study; run with bun scripts/ci-runtime-bench.ts.
import {bool, fun, oneOf, when} from '../core/dsl.ts'

export function study(name: string, make: () => any, inputs: any[], plain: (x: any) => any, normalize: (x: any) => number) {
  const N = Number(process.env.BENCH_N ?? 100000), C = Number(process.env.BENCH_COLD ?? 1000)
  const model = make(), rule = model.rule, runtime = rule.interpreter()
  const interpreted = (x: any) => { const ps = rule.encodeParams({}); return rule.decode(runtime.step(ps, runtime.init(ps), rule.encodeInput(x, {}))) }
  const compiled = model.compiled?.() ?? ((x: any) => model.run(x))
  const unpack = (x: any) => Object.fromEntries(Object.entries(x).map(([k,v]) => [k.replace(/^out\./, ''),v]))
  const cases = [ ['plain', plain], ['compiled', compiled], ['interpreter', (x: any) => unpack(interpreted(x))] ] as const
  for (const x of inputs) { const want = JSON.stringify(normalize(plain(x))); for (const [label, f] of cases) if (JSON.stringify(normalize(f(x))) !== want) throw Error(`${name}: ${label} mismatch`) }
  for (const [label,f] of cases) {
    let sum=0; for(let i=0;i<Math.min(N,20000);i++) sum+=normalize(f(inputs[i%inputs.length]))
    const start=performance.now(); sum=0; for(let i=0;i<N;i++) sum+=normalize(f(inputs[i%inputs.length])); const ns=(performance.now()-start)*1e6/N
    console.log(JSON.stringify({name,mode:label,n:N,nsPerOp:ns,checksum:sum}))
  }
  for (const mode of ['compiled','interpreter'] as const) {
    let sum=0; const start=performance.now(); for(let i=0;i<C;i++) { const m=make(), x=inputs[i%inputs.length]; if(mode==='compiled') sum+=normalize(m.compiled ? m.compiled()(x) : m.run(x)); else { const r=m.rule, g=r.interpreter(), p=r.encodeParams({}); sum+=normalize(unpack(r.decode(g.step(p,g.init(p),r.encodeInput(x,{}))))) } }
    console.log(JSON.stringify({name,mode:mode+'-cold-model-create-first-call',n:C,nsPerOp:(performance.now()-start)*1e6/C,checksum:sum}))
  }
}

if (import.meta.main) {
  const inputs4 = ['a','b','c','d'].map(k=>({k}))
  study('synthetic-4',()=>fun('four').inputs({k:oneOf('a','b','c','d')}).returns(({k})=>({out:when(k.is('a'),'b',k)})),inputs4,x=>{ if(x.k==='a') return {out:'b'}; return {out:x.k} },x=>'abcd'.indexOf(x.out))
  const inputs128=Array.from({length:128},(_,i)=>Object.fromEntries(Array.from({length:7},(_,b)=>['b'+b,!!(i&(1<<b))])))
  study('synthetic-128',()=>fun('128').inputs({b0:bool,b1:bool,b2:bool,b3:bool,b4:bool,b5:bool,b6:bool}).returns(({b0,b1,b2,b3,b4,b5,b6})=>({out:when(b0.not().or(b1),1,when(b2.and(b3,b4.not()).or(b5.and(b6.not())),2,0))})),inputs128,x=>{ if(!x.b0||x.b1) return {out:1}; if(x.b2&&x.b3&&!x.b4||x.b5&&!x.b6) return {out:2}; return {out:0} },x=>x.out)
  const inputs32=Array.from({length:32},(_,i)=>Object.fromEntries(Array.from({length:5},(_,b)=>['b'+b,!!(i&(1<<b))])))
  study('synthetic-32',()=>fun('32').inputs({b0:bool,b1:bool,b2:bool,b3:bool,b4:bool}).returns(({b0,b1,b2,b3,b4})=>({out:b0.and(b1.not(),b2,b3.iff(b4))})),inputs32,x=>({out:x.b0&&!x.b1&&x.b2&&x.b3===x.b4}),x=>Number(x.out))
}
