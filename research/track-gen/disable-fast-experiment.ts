// Disposable control only: preserve row reuse, disable the separate compiled sampler.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.env.TRACK_GEN_DISPOSABLE!=='1')throw Error('disposable snapshot only')
const file='core/sample-step.ts',text=readFileSync(file,'utf8'),anchor='if (++calls === 1000) {'
if(!text.includes(anchor))throw Error('source mismatch')
writeFileSync(file,text.replace(anchor,'if (++calls === -1) {'))
