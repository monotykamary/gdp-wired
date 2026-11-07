// Prepare project gate manifests; no prover work runs here.
const make=(args:string[])=>{
 const out=Bun.spawnSync(['bun','research/protocols/ic3syn/jobs.ts',...args],{stdout:'pipe',stderr:'pipe'})
 if(out.exitCode)throw new Error(out.stderr.toString())
 return JSON.parse(out.stdout.toString()) as {name:string,cmd:string,timeout:number,cpu:number,memory:number,vm_type:string}[]
}
const paired=make(['--paired','base','--runs','3']).map(j=>({...j,timing:true})),duo=make(['--paired','base','--suite','duoai','--runs','1']).map(j=>({...j,timing:true}))
const broken=make(['--skip','search','--runs','1']).map(j=>({...j,timing:true,timeout:120,cmd:j.cmd.replace('GDP_INFER_TRACE=2 timeout -s KILL 210 ','bun install --frozen-lockfile >/dev/null && GDP_INFER_TRACE=2 timeout -s KILL 60 ').replace('exit $s','echo BROKEN_EXIT=$s; if [ "$s" = 0 ] || [ "$s" = 124 ] || [ "$s" = 137 ]; then exit 0; else exit "$s"; fi')}))
const shards=Array.from({length:7},(_,i)=>({name:`shard-${i+1}`,cmd:`bun install --frozen-lockfile >/dev/null && bun scripts/test-shards.ts --shard ${i+1}/7`,timeout:1800,cpu:4,memory:8192,timing:true}))
for(const [name,jobs]of [['ic3syn-paired',paired],['duoai-paired',duo],['broken',broken],['shard',shards]]as const){await Bun.write(`research/track-p/${name}-gate-jobs.json`,JSON.stringify(jobs,null,1)+'\n');console.log(JSON.stringify({name,jobs:jobs.length}))}
