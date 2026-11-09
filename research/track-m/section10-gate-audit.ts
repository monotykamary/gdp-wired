// Recompute the reported table from the six retained fresh-process receipts.
export function auditSection10Gate(records:any[],manifest:any,expectedBaseline='50109a36'){
 if(!manifest.kernelEqual||!manifest.harnessEqual||!String(manifest.baselineCommit).startsWith(expectedBaseline))throw new Error('baseline/kernel/harness drift')
 if(JSON.stringify(records.map(r=>r.id))!==JSON.stringify(['A1','B1','A2','B2','A3','B3']))throw new Error('not three interleaved repeats')
 const names:string[]=records[0].laws.map((l:any)=>l.law)
 if(names.length!==5||new Set(names).size!==5)throw new Error('not five unique laws')
 for(const r of records){
  if(r.exitCode!==0||r.side!==r.id[0]||r.repeat!==Number(r.id[1])||JSON.stringify(r.laws.map((l:any)=>l.law))!==JSON.stringify(names))throw new Error('incomplete or mislabeled process')
  if(!Number.isFinite(r.total?.wallMs)||r.total.wallMs<0)throw new Error('missing family wall')
  for(const l of r.laws)if(!Number.isFinite(l.wallMs)||l.wallMs<0||!Number.isFinite(l.countedMs)||l.countedMs<0||typeof l.proven!=='boolean'||typeof l.checked!=='boolean')throw new Error('invalid law receipt')
 }
 const median=(xs:number[])=>[...xs].sort((a,b)=>a-b)[1]!,project=(rs:any[])=>({verdicts:rs.map(r=>({proven:r.proven,checked:r.checked})),countedUnits:rs.map(r=>r.countedMs),wallMedianMs:median(rs.map(r=>r.wallMs)),wallMaxMs:Math.max(...rs.map(r=>r.wallMs))})
 const laws=names.map((law:string)=>{const a=records.filter(r=>r.side==='A').map(r=>r.laws.find((l:any)=>l.law===law)),b=records.filter(r=>r.side==='B').map(r=>r.laws.find((l:any)=>l.law===law));return {law,A:project(a),B:project(b),noRegression:a.every((r:any,i:number)=>!r.checked||b[i].checked)}})
 const families=Object.fromEntries(['A','B'].map(side=>{const rs=records.filter(r=>r.side===side),walls=rs.map(r=>r.total.wallMs);return [side,{wallMedianMs:median(walls),wallMaxMs:Math.max(...walls),wallMs:walls,checkedCounts:rs.map(r=>r.laws.filter((l:any)=>l.proven&&l.checked).length)}]})),b=records.filter(r=>r.side==='B')
 return {baseline:manifest.baselineCommit,kernelEqual:true,harnessEqual:true,laws,families,noRegression:laws.every(l=>l.noRegression),gate1ReplayPass:b.every(r=>r.total.wallMs<60000&&r.laws.every((l:any)=>l.proven&&l.checked)),laterGatesRun:false}
}
