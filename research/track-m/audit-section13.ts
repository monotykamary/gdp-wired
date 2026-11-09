// Independent arithmetic/ledger audit of the trimmed primary receipts.
import {readFileSync,readdirSync,writeFileSync,mkdtempSync} from 'node:fs'
import {join} from 'node:path'
import {homedir} from 'node:os'
import {strict as assert} from 'node:assert'
const input=process.argv[2];if(!input)throw new Error('INPUT required')
const sum=(xs:number[])=>xs.reduce((a,b)=>a+b,0),near=(a:number,b:number)=>Math.abs(a-b)<1e-6
const rows:any[]=[]
for(const name of readdirSync(input).filter(n=>/^Inv(?:star|2973)-op\d+\.json$/.test(n)).sort()){
 const r=JSON.parse(readFileSync(join(input,name),'utf8'));assert(!('columns'in r));assert(r.researchOnly&&Number.isFinite(r.units)&&Number.isFinite(r.wallMs));assert(near(sum(r.ledger.map((x:any)=>x.units))+r.outsideActions,r.units));assert(r.closed===(r.verdict==='closed'))
 for(const k of ['cuts','sat','refuted','unknown','reused'])assert.equal(sum(r.ledger.map((x:any)=>x[k])),r.stats[k])
 const f=r.firstFailure,c=f?.capture;let validation:any={model:false,exactViolatedSet:false,path:false}
 if(c?.model){
  const model=c.model as Record<string,number>,value=(name:string)=>{const n=model[name]??0;assert(Number.isSafeInteger(n));return BigInt(n)}
  for(const [,atom]of c.path){let n=0n;for(const [key,k]of Object.entries(atom.lin)){assert(Number.isSafeInteger(k));n+=BigInt(k as number)*(key==='1'?1n:value(key))}assert.equal(n<=0n,atom.holds)}
  const below=(e:any):bigint=>{if(e.op==='var')return value(e.name);if(e.op==='const')return BigInt(e.value);if(e.op==='add')return below(e.a)+below(e.b);if(e.op==='mul')return BigInt(e.k)*below(e.a);throw new Error('unsupported exact bound '+e.op)}
  const expected=c.pool.filter((index:number)=>{const inst=c.cert.insts[index];return sumBig(inst.terms.map(([k,n]:[number,string])=>BigInt(k)*value(n)))+BigInt(inst.unit)*below(inst.below)>0n})
  assert.deepEqual(expected,c.violated);assert.deepEqual(r.sources.map((s:any)=>s.index),c.violated)
  for(const source of r.sources)assert(near(sum(source.attempts.map((a:any)=>a.units)),source.units))
  validation={model:true,exactViolatedSet:true,path:true,note:'Exact BigInt path/instance audit; complete numeric-model validation was performed before production recorded it.'}
 }else if(!r.closed){assert.equal(r.sources.length,0)}
 const sourceResults=r.sources.map((s:any)=>({index:s.index,result:s.result,units:s.units,attempts:s.attempts.length})),scope=f?{kind:f.kind,reason:f.reason,phase:f.phase,path:c?.path??f.path,model:c?.model??null,violatedSet:c?.violated??[],sourceResults}:null
 rows.push({law:r.law,name:r.name,op:r.op,verdict:r.verdict,units:r.units,wallMs:r.wallMs,allowance:r.allowance,limit:r.limit,stats:r.stats,ledger:r.ledger,firstFailure:scope,validation,publication:r.publication})
}
assert.equal(rows.length,11)
const output={researchOnly:true,engine:'5974b9165d6860f1157f3bed3cd66a7e1514e904',allowancePerOp:50000,wallLimitMs:600000,noCompleteLawClaim:true,rows}
const out=mkdtempSync(join(homedir(),'track-m-section13-audit-'));writeFileSync(join(out,'summary.json'),JSON.stringify(output,null,2)+'\n');console.log(JSON.stringify({auditPassed:true,ops:rows.length,closed:rows.filter(r=>r.verdict==='closed').map(r=>[r.name,r.op]),summary:join(out,'summary.json')}))
const child=Bun.spawn(['bun','research/track-m/pack-section10-archive.ts',join(out,'summary.json')],{stdout:'inherit',stderr:'inherit'});if(await child.exited)throw new Error('archive failed')
function sumBig(xs:bigint[]):bigint{return xs.reduce((a,b)=>a+b,0n)}
