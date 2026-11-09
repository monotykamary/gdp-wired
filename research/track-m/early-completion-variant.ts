// Research-only scheduling of the existing bounded count-law completion.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.env.LAB_DISPOSABLE!=='1')throw Error('LAB_DISPOSABLE=1 required')
let source=readFileSync('core/counts.ts','utf8')
const block=`    let countCompleted = false
    const completeCounts = (): boolean => {
      if (!pass || countCompleted) return false
      countCompleted = true
      const completion = completeCountLawInstances(modelLaws, at, ts, l => reads(l.holds, isCount).size > 0, generation.tick)
      if (!completion.added.length) return false
      at = completion.at
      tally('#count-completion', completion.added.length)
      countsDump.on?.({law: law.name, pass, phase: 'count-completion', added: completion.added})
      return true
    }
`
if(source.split(block).length!==2)throw Error('non-unique completion block')
source=source.replace(block,'')
const anchor='    let built = build()'
if(source.split(anchor).length!==2)throw Error('non-unique initial build')
source=source.replace(anchor,block+'    if (pass && reads(law.holds, isCount).size) completeCounts()\n'+anchor)
writeFileSync('core/counts.ts',source)
console.log(JSON.stringify({variant:'early-count-law-completion',maxTuples:48,maxTerms:4}))
