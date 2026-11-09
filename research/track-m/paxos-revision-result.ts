import {readFileSync} from 'node:fs'
const [revision,repeat,code,start,end,file]=process.argv.slice(2)
const row=readFileSync(file!,'utf8').split('\n').flatMap(line=>{try{return [JSON.parse(line)]}catch{return []}}).find(r=>r.id==='paxos_epr')
const wallMs=Number(BigInt(end!)-BigInt(start!))/1e6,exit=Number(code),verdict=[124,137].includes(exit)?'timeout':row?.search?.verdict??'missing'
const strict=exit===0&&verdict==='proven'&&row.search.ms<=60000&&wallMs<=60000
console.log(JSON.stringify({revision,repeat:Number(repeat),exit,verdict,strict,wallMs,search:row?.search?{ms:row.search.ms,why:row.search.why,goal:row.search.goal,work:row.search.work,full:row.search.full,found:row.search.found?.length,lastFound:row.search.found?.slice(-6)}:undefined,error:row?.error,affinity:readFileSync('/proc/self/status','utf8').match(/^Cpus_allowed_list:\s*(.+)$/m)?.[1]?.trim()}))
if(process.env.PAXOS_REQUIRE_PROVEN==='1'&&!strict)process.exitCode=1
