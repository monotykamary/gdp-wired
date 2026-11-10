// Per-root-call CPU/wall diagnostics; no query or proof mutation.
import {readFileSync,writeFileSync} from 'node:fs'
let file='research/track-m/phase-census-meter.ts',s=readFileSync(file,'utf8')
const replace=(a:string,b:string)=>{if(s.split(a).length!==2)throw new Error('check-call marker '+a);s=s.replace(a,b)}
replace(' readonly sites=new Map'," readonly checkCalls:{site:string,wallMs:number,cpuMs:number}[]=[]\n readonly sites=new Map")
replace('this.sites.clear();', 'this.checkCalls.length=0;this.sites.clear();')
replace('this.enter(phase,site);try{return f()}finally{this.leave()}',"this.enter(phase,site);const watch=site==='kernel/kernel.ts:check'||site==='kernel/kernel.ts:checkMC',start=watch?performance.now():0,cpu=watch?process.cpuUsage():undefined;try{return f()}finally{if(watch){const used=process.cpuUsage(cpu!);this.checkCalls.push({site,wallMs:performance.now()-start,cpuMs:(used.user+used.system)/1000})}this.leave()}")
writeFileSync(file,s)
file='research/track-m/run-phase-census.ts';s=readFileSync(file,'utf8')
s=s.replace('for(const prefix of prefixes){',"for(const prefix of prefixes.filter((_,i)=>process.env.LAB_PROFILE_LIMIT_PROVED!=='1'||i<3)){")
s=s.replace('sites:snapshot.sites,traceEvents:', 'sites:snapshot.sites,checkCalls:census.checkCalls.slice(),traceEvents:')
writeFileSync(file,s)
