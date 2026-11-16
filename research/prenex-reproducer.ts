// Run this same script against old and fixed sources. Old sources exit 1.
import {rule,nat,everyKey,proveRule} from '../core/dsl.ts'
import {interpret} from '../core/machine.ts'
const r=rule('nested counterexample').inputs({k:nat,v:nat}).maps({M:0}).state({n:0}).step(({M,k,v,n})=>({M:M.set(k,v),n}))
const run=interpret(r.machine),state=run.step({},run.init({}),{k:0,v:1})
if(state.maps.M!.get(0)!==1||(state.maps.M!.get(1)??0)!==0)throw Error('missing explicit counterexample')
try {
 const law=r.law('false nested law',({M})=>everyKey(a=>everyKey(b=>M.at(a).atMost(M.at(b)))))
 const verdict=proveRule(r as never,[law],{search:false})
 console.log(JSON.stringify({trace:[{k:0,v:1}],counterexample:{a:0,b:1},law,verdict}))
 if(verdict.proven)process.exitCode=1
} catch(error) {
 if(!(error instanceof Error)||!('kind' in error)||error.kind!=='quantifier-admission')throw error
 console.log(JSON.stringify({trace:[{k:0,v:1}],counterexample:{a:0,b:1},refused:{name:error.name,message:error.message}}))
}
