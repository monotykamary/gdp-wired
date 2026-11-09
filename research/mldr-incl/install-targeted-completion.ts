// Changes only a disposable boat checkout; never invoked by production.
import {readFileSync,writeFileSync} from 'node:fs'
const path='core/counts.ts';let text=readFileSync(path,'utf8')
const edits:[string,string][]=[
 ["import {preferMemberInclusions} from './count-recovery/member-inclusions.ts'","import {preferMemberInclusions} from './count-recovery/member-inclusions.ts'\nimport {targetedCompletion} from '../research/mldr-incl/targeted-completion.ts'"],
 ['    let countCompleted = false','    let countCompleted = false, targetedCount = 0'],
 ['      const completion = completeCountLawInstances(modelLaws, at, ts, l => reads(l.holds, isCount).size > 0, generation.tick)','      let emitted=0\n      const completion = completeCountLawInstances(modelLaws, at, ts, l => reads(l.holds, isCount).size > 0, () => emitted++ < 48-targetedCount && generation.tick())'],
 ['    let decideStep = decisions.get(id)','    const targetStep=built.at(-1)\n    if(pass&&!supported&&targetStep){\n      const seed=targetedCompletion(m,modelLaws,at,ts,targetStep.decls,targetStep.c,generation.tick)\n      if(seed.added.length){at=seed.at;targetedCount=seed.added.length;tally("#targeted-completion",targetedCount);countsDump.on?.({phase:"targeted-completion",added:seed.added});built=build()}\n    }\n    let decideStep = decisions.get(id)'],
]
for(const [a,b]of edits){if(text.split(a).length!==2)throw Error('non-unique experiment anchor');text=text.replace(a,b)}
writeFileSync(path,text)
