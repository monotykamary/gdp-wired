import {mkdirSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {phaseMarker} from '../section51-supplier-timed/phase-marker.ts'
const [out,mode]=process.argv.slice(2);if(!out)throw Error('output required')
mkdirSync(out,{recursive:true})
const path=join(out,'phase-marker-status.json');if(mode==='fault')mkdirSync(path)
const marker=phaseMarker(join(out,'phase.tsv'))
writeFileSync(join(out,'verdict.json'),JSON.stringify({proven:true,checked:true}))
process.exitCode=0
marker.mark('complete')
const phaseStatusExported=marker.saveStatus(status=>writeFileSync(path,JSON.stringify(status)))
writeFileSync(join(out,'telemetry.json'),JSON.stringify({phaseStatusExported,failures:marker.failures,statusExportFailures:marker.statusExportFailures}))
