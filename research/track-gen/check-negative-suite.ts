import {readFileSync,readdirSync,writeFileSync} from 'node:fs'
const suite=process.argv[2]??'runs/track-gen-negative-suite-v1',paxos=process.argv[3]??'runs/track-gen-negative-paxos-v1',errors:string[]=[]
type Side={exit?:number,verdict?:string,ms?:number,why?:string}
const rows:{file:string,id:string,run:number,cand:Side,base:Side}[]=[]
for(const dir of [suite,paxos])for(const file of readdirSync(dir).filter(f=>f.endsWith('.log'))){const row={file,id:'',run:0,cand:{} as Side,base:{} as Side};let side:'cand'|'base'|undefined
 for(const line of readFileSync(`${dir}/${file}`,'utf8').split('\n')){const b=/^PAIR begin side=(cand|base) id=(\S+) run=(\d+)/.exec(line),e=/^PAIR end side=(cand|base) exit=(\d+)/.exec(line);if(b){side=b[1] as 'cand'|'base';row.id=b[2]!;row.run=Number(b[3])}else if(e){row[e[1] as 'cand'|'base'].exit=Number(e[2]);side=undefined}else if(side&&line.startsWith('{"id"')){const r=JSON.parse(line);if(r.error)errors.push(`${file}/${side}: ${r.error}`);Object.assign(row[side],r.broken)}}
 for(const name of ['base','cand'] as const){const r=row[name];if(![0,124,137].includes(r.exit??-1)||r.exit===0&&!r.verdict)errors.push(`${file}/${name}: incomplete`);if(r.verdict==='proven')errors.push(`${file}/${name}: broken variant proven`)}rows.push(row)
}
if(rows.length!==87||new Set(rows.map(r=>`${r.id}:${r.run}`)).size!==87)errors.push('expected 87 distinct negative pairs')
const refuted=(r:Side)=>r.exit===0&&r.verdict==='refuted',refutationLosses=rows.filter(r=>refuted(r.base)&&!refuted(r.cand)).map(r=>r.file),completionDeltas=rows.filter(r=>r.base.exit===0&&r.cand.exit!==0).map(r=>({file:r.file,base:r.base,cand:r.cand,status:'OPEN'}))
const result={passed:!errors.length&&!refutationLosses.length,baseline:'6a3874d3',strictMs:60000,policy:'Refutation losses and false proofs block; UNKNOWN-to-timeout cost-only deltas remain OPEN per coordinator.',pairs:rows.length,baselineRefuted:rows.filter(r=>refuted(r.base)).length,candidateRefuted:rows.filter(r=>refuted(r.cand)).length,refutationLosses,completionDeltas,errors,rows}
writeFileSync(`${suite}/verified.json`,JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify({...result,rows:undefined}));if(!result.passed)process.exitCode=1
