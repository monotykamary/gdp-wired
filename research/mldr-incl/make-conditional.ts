import {writeFileSync} from 'node:fs'
const jobs=[]
for(const variant of ['base','preferred'])for(const support of ['no','yes'])for(const ms of [1000,2700,5000])for(const repeat of [1,2]){
 const capture=ms===2700&&support==='yes'&&repeat===1,patch=variant==='base'?'git apply -R research/mldr-incl/proposal.diff; ':''
 const run=`${capture?'DUMP_DIR=/tmp/conditional DUMP_MIN=0 DUMP_N=10000 DUMP_ALL=1 ':''}timeout -s KILL 45 bun ${capture?'--preload ./research/query/dump.ts --preload ./research/track-p/capture.ts ':''}research/mldr-incl/conditional-safety.ts inputs/family-first.json ${ms} ${support} ${repeat}`
 jobs.push({name:`${variant}-${support}-${ms}-r${repeat}`,cmd:`set -e; bash research/track-m/prepare-vendors.sh; bun install --frozen-lockfile >/dev/null; ${patch}${run}${capture?'; bun research/mldr-incl/pack-capture.ts /tmp/conditional':''}`,cpu:8,memory:14336,timeout:90})
}
writeFileSync('research/mldr-incl/conditional-jobs.json',JSON.stringify(jobs,null,2)+'\n');console.log(JSON.stringify({jobs:jobs.length,conditional:true}))
