import {readFileSync,writeFileSync} from 'node:fs'
const root=process.argv[2]??'runs/track-gen-negative-paxos-v1',errors:string[]=[]
type Side={exit?:number,verdict?:string,ms?:number,why?:string}
const rows=[1,2,3].map(run=>{const sides:{cand:Side,base:Side}={cand:{},base:{}};let side:'cand'|'base'|undefined
 for(const line of readFileSync(`${root}/negative-paxos-r${run}.log`,'utf8').split('\n')){const b=/^PAIR begin side=(cand|base)/.exec(line),e=/^PAIR end side=(cand|base) exit=(\d+)/.exec(line);if(b)side=b[1] as 'cand'|'base';else if(e){sides[e[1] as 'cand'|'base'].exit=Number(e[2]);side=undefined}else if(side&&line.startsWith('{"id"')){const r=JSON.parse(line);if(r.error)errors.push(`r${run}/${side}: ${r.error}`);Object.assign(sides[side],r.broken)}}
 for(const name of ['base','cand'] as const){const r=sides[name];if(![0,124,137].includes(r.exit??-1)||r.exit===0&&!r.verdict)errors.push(`r${run}/${name}: incomplete`);if(r.verdict==='proven')errors.push(`r${run}/${name}: broken variant proven`)}
 return {run,...sides}
})
const completionLosses=rows.filter(r=>r.base.exit===0&&r.cand.exit!==0).map(r=>r.run)
const result={passed:!errors.length&&!completionLosses.length,baseline:'6a3874d3',strictMs:60000,errors,completionLosses,rows}
writeFileSync(`${root}/verified.json`,JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify(result));if(!result.passed)process.exitCode=1
