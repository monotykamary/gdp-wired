type Stats=Record<string,number>
type Row={law:string,proven:boolean,checked:boolean,wallMs:number,countedMs:number,cache:Stats|null}
type Run={id:string,side:string,repeat:number,exitCode:number,laws:Row[],total:{wallMs:number}}
const prefixes=['one primary','Inv3915','Inv1758','Inv2973','Inv*']
const finite=(x:number)=>Number.isFinite(x)&&x>=0
const median=(xs:number[])=>[...xs].sort((a,b)=>a-b)[1]!
const same=(a:unknown,b:unknown)=>JSON.stringify(a)===JSON.stringify(b)
export function auditCostWins(runs:Run[],manifest:{baselineCommit:string,kernelEqual:boolean,harnessEqual:boolean}){
 if(!manifest.baselineCommit.startsWith('50109a36')||!manifest.kernelEqual||!manifest.harnessEqual)throw new Error('baseline/kernel/harness identity failure')
 if(!same(runs.map(r=>r.id),['A1','B1','A2','B2','A3','B3']))throw new Error('missing or reordered interleaved repeats')
 const names=runs[0]!.laws.map(r=>r.law)
 if(names.length!==5||new Set(names).size!==5||prefixes.some(p=>names.filter(n=>n.startsWith(p)).length!==1))throw new Error('wrong five-law family')
 for(const r of runs){
  if(r.id!==r.side+r.repeat||r.exitCode!==0||!same(r.laws.map(l=>l.law),names))throw new Error('incomplete run '+r.id)
  for(const l of r.laws){
   if(!finite(l.countedMs)||!finite(l.wallMs)||l.proven!==l.checked)throw new Error('invalid verdict/cost')
   if(r.side==='B'){
    if(!l.cache||!Object.values(l.cache).every(v=>Number.isSafeInteger(v)&&v>=0))throw new Error('missing or invalid candidate counters')
    if(!(l.cache.retargetHits!<=l.cache.retargetChecks!)||!(l.cache.independentHits!<=l.cache.independentChecks!))throw new Error('impossible cache hit count')
   }
  }
 }
 const laws=prefixes.map(prefix=>{
  const name=names.find(n=>n.startsWith(prefix))!,a=runs.filter(r=>r.side==='A').map(r=>r.laws.find(l=>l.law===name)!),b=runs.filter(r=>r.side==='B').map(r=>r.laws.find(l=>l.law===name)!)
  if([...a,...b].some(r=>r.proven!==a[0]!.proven||r.checked!==a[0]!.checked))throw new Error('verdict mismatch: '+name)
  const project=(rs:Row[])=>({countedUnits:rs.map(r=>r.countedMs),wallMedianMs:median(rs.map(r=>r.wallMs)),wallMaxMs:Math.max(...rs.map(r=>r.wallMs)),cache:rs.map(r=>r.cache)})
  return {law:name,proven:a[0]!.proven,checked:a[0]!.checked,A:project(a),B:project(b)}
 })
 return {baseline:manifest.baselineCommit,order:runs.map(r=>r.id),lawResults:runs.length*5,allVerdictsIdentical:true,laws,laterGatesRun:false}
}
