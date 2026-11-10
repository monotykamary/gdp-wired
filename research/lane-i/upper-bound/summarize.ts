// Research census aggregation. Missing data is pending, never a success.
import {existsSync,readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
export function parseUpperLog(text:string){
 const rows=(prefix:string)=>text.split('\n').filter(l=>l.startsWith(prefix+' ')).map(l=>JSON.parse(l.slice(prefix.length+1)))
 const results=rows('UPPER_RESULT'),verifiers=rows('UPPER_VERIFY'),censored=rows('UPPER_CENSORED'),progress=rows('UPPER_PROGRESS'),issues:string[]=[]
 if(results.length>1)issues.push('multiple terminal records')
 const result=results.at(-1),last=result?.progress??censored.at(-1)??progress.at(-1),verified=verifiers.length===1&&verifiers[0].checked===true
 let status=result?.status??(censored.length?'censored':'pending')
 if((status==='closed'||result?.checked)&&(!result?.checked||!verified)){status='unknown';issues.push('missing/failed independent check')}
 if(results.length>1)status='unknown'
 if(!['closed','unknown','sat','censored','pending'].includes(status)){status='unknown';issues.push('invalid terminal status')}
 if(result&&(result.familySize!==34||result.suppliedLaws?.length!==0||!result.originalFamily||!result.noShare)){status='unknown';issues.push('invalid original-family contract')}
 if(result?.error||result?.checkError)issues.push(result.error??result.checkError)
 const rss=Number(/Maximum resident set size \(kbytes\):\s*(\d+)/.exec(text)?.[1]??0)
 return {status,verified,issues,result,peakRssKiB:Math.max(rss,result?.peakRssKiB??last?.peakRssKiB??0),countedUnits:result?.countedUnits??last?.countedUnits,countedUnitsLowerBound:!result,wallMs:result?.wallMs??last?.wallMs,lastLeaf:last?.leaf??null,lastEvent:last?.last??null,excludedCount:last?.excludedCount??null,excluded:last?.excluded??null}
}
if(import.meta.main){
 const dir=process.argv[2];if(!dir)throw Error('RESULT DIRECTORY required')
 const jobs=JSON.parse(readFileSync(new URL('./jobs.json',import.meta.url),'utf8')),placement=existsSync(join(dir,'placement.json'))?JSON.parse(readFileSync(join(dir,'placement.json'),'utf8')):{}
 const summary=jobs.map((j:{name:string})=>{const path=join(dir,j.name+'.log'),data=parseUpperLog(existsSync(path)?readFileSync(path,'utf8'):'');return {name:j.name,cpu:placement[j.name]?.cpu,...data}})
 const counts=Object.fromEntries(['closed','unknown','sat','censored','pending'].map(status=>[status,summary.filter((r:any)=>r.status===status).length]))
 writeFileSync(join(dir,'upper-summary.json'),JSON.stringify({researchOnly:true,counts,rows:summary},null,2)+'\n')
 writeFileSync(join(dir,'upper-summary.tsv'),['shard\tstatus\tcounted_units\twork_is_lower_bound\twall_ms\tpeak_rss_kib\texcluded\tlast_stage\tcpu',...summary.map((r:any)=>[r.name,r.status,r.countedUnits??'',r.countedUnitsLowerBound,r.wallMs??'',r.peakRssKiB,r.excludedCount??'',r.lastEvent?.stage??r.lastEvent?.phase??'',r.cpu??r.result?.cpu??''].join('\t'))].join('\n')+'\n')
 console.log(JSON.stringify({researchOnly:true,expected:jobs.length,counts,issues:summary.flatMap((r:any)=>r.issues.map((issue:string)=>({shard:r.name,issue})))}))
}
