// Isolated ordering experiment, used only in a disposable boat job.
import {readFileSync,writeFileSync} from 'node:fs'
const file='core/counts.ts';let source=readFileSync(file,'utf8')
for(const [a,b]of [
 ['    let built = build()','    let built: ReturnType<typeof build>'],
 ['    let decideStep = decisions.get(id)','    if (!supported && !reads(law.holds, isCount).size && m.inputMaps?.length) completeCounts()\n    built = build()\n    let decideStep = decisions.get(id)'],
] as [string,string][]){if(source.split(a).length!==2)throw new Error('non-unique experiment anchor');source=source.replace(a,b)}
writeFileSync(file,source)
