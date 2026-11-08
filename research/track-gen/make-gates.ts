// Manifest construction only. All prover processes run on boat.
import {spawnSync} from 'node:child_process'
type Job={name:string,cmd:string,timeout:number,cpu:number,memory:number}
function make(args:string[]):Job[]{const r=spawnSync('bun',['research/protocols/ic3syn/jobs.ts',...args],{encoding:'utf8'});if(r.status)throw Error(r.stderr);return JSON.parse(r.stdout)}
const prepare='set -e; mkdir -p base; tar -xf replay-input/main.tar -C base; '
for(const [name,args] of [['ic3syn',['--paired','base','--runs','3']],['duoai',['--paired','base','--suite','duoai','--runs','1']]] as const){
 const jobs=make([...args]).map(j=>({...j,cmd:prepare+j.cmd.replaceAll('timeout -s KILL','taskset -c 0-3 timeout -s KILL'),cpu:8,memory:14336,timeout:300}))
 await Bun.write(`research/track-gen/${name}-jobs.json`,JSON.stringify(jobs,null,1)+'\n');console.log(`${name}: ${jobs.length}`)
}
const broken=make(['--skip','search','--runs','1']).map(j=>({...j,cpu:8,memory:14336,timeout:180,cmd:'set -e; bun install --frozen-lockfile >/dev/null; set +e; '+j.cmd.replace('timeout -s KILL 210','taskset -c 0-3 timeout -s KILL 60').replace('exit $s','echo BROKEN_EXIT=$s; if [ "$s" = 0 ] || [ "$s" = 124 ] || [ "$s" = 137 ]; then exit 0; else exit "$s"; fi')}))
await Bun.write('research/track-gen/broken-jobs.json',JSON.stringify(broken,null,1)+'\n');console.log(`broken: ${broken.length}`)
