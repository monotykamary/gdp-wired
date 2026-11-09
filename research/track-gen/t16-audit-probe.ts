// Focused reproductions of Lane D's c9d7f823 audit findings. No proof claim.
import {readFileSync} from 'node:fs'
import {type Machine, type Law, n, x, get, same} from '../../core/machine.ts'
import {finiteModelChecker} from '../../core/finite-model.ts'
import {WallExpired} from '../../core/wall.ts'
import {withWall} from '../../kernel/prove.ts'
const machine: Machine = {name:'cancelled completion',params:['N'],inputs:[],state:{value:n(0)},counts:{Total:{j:'row',key:'member',below:x('N'),body:n(1)}},step:{state:{value:n(0)}}}
const law:Law = {name:'total',holds:same(get('Total',n(0)),x('N'))}
const check=finiteModelChecker(machine)
for(let i=0;i<3;i++)check([law],law,{N:1000,value:0})
const rows=[]
for(const stopOnly of [false,true])for(let repeat=1;repeat<=3;repeat++){
 const start=performance.now(),end=start+20
 let outcome='completed',reason:string|undefined
 try{const r=withWall(start+(stopOnly?1000:20),()=>check([law],law,{N:5_000_000,value:0},()=>stopOnly&&performance.now()>=end));outcome=r.genuine?'genuine':'uncertified';if(!r.genuine)reason=r.reason}
 catch(error){if(!(error instanceof WallExpired))throw error;outcome='wall';reason=error.phase}
 const elapsedMs=performance.now()-start
 if(stopOnly?reason!=='attempt exhausted':outcome!=='wall'||reason!=='derived count')throw Error('inner cancellation not observed')
 rows.push({stopOnly,repeat,bound:5_000_000,budgetMs:20,elapsedMs,outcome,reason})
}
const facts:Machine={name:'declared fact',params:['p'],inputs:[],state:{value:n(0)},facts:[{name:'p zero',holds:same(x('p'),n(0))}],step:{state:{value:x('p')}}}
const zero:Law={name:'zero',holds:same(x('value'),n(0))},rejected=finiteModelChecker(facts)([zero],zero,{p:1,value:0})
if(rejected.genuine||rejected.reason!=='declared fact is false')throw Error('invalid fact accepted')
console.log(JSON.stringify({scope:'focused audit regressions, not a final gate',revision:process.env.SOURCE_COMMIT,cpu:readFileSync('/proc/cpuinfo','utf8').match(/^model name\s*:\s*(.+)$/m)?.[1],rows,factProbe:rejected},null,2))
