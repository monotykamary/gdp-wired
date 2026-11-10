// Research-only initial row bridges; no count-policy or kernel change.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.env.LAB_DISPOSABLE!=='1')throw Error('LAB_DISPOSABLE=1 required')
let source=readFileSync('core/counts.ts','utf8')
const edits:[string,string][]=[
 ["import {preferMemberInclusions} from './count-recovery/member-inclusions.ts'","import {preferMemberInclusions} from './count-recovery/member-inclusions.ts'\nimport {instantiateRowPremises} from './count-recovery/row-premises.ts'"],
 ["    let wide = false",`    if(pass&&law.forall&&(law.keys?.length??0)===2&&!reads(law.holds,isCount).size){
      const own=[v(law.forall+'#'),...(law.keys??[]).map(v)]
      const seeded=instantiateRowPremises(m,ls,law,at,own,keyed,64-seedCount,generation.tick)
      at=seeded.at;seedCount+=seeded.added.length
      if(seeded.added.length)countsDump.on?.({phase:'row-premises',law:law.name,pass,added:seeded.added})
    }
    let wide = false`],
]
for(const [before,after]of edits){if(source.split(before).length!==2)throw Error('non-unique row variant anchor');source=source.replace(before,after)}
writeFileSync('core/counts.ts',source)
console.log(JSON.stringify({variant:'initial-row-premises',edits:edits.length}))
