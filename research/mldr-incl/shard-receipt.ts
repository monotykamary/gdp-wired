export function parseShardReceipt(text:string){
 const sum=(word:string)=>[...text.matchAll(new RegExp(`^\\s*(\\d+) ${word}\\s*$`,'gm'))].reduce((n,m)=>n+Number(m[1]),0)
 const runs=[...text.matchAll(/^Ran (\d+) tests across (\d+) files?[.] /gm)].map(m=>({tests:Number(m[1]),files:Number(m[2])})),pass=sum('pass'),fail=sum('fail'),skip=sum('skip')
 return {pass,fail,skip,runs,complete:!!runs.length&&runs.reduce((n,r)=>n+r.tests,0)===pass+fail+skip}
}
