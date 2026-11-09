import {readFileSync,writeFileSync} from 'node:fs'
if(process.env.TRACK_GEN_DISPOSABLE!=='1')throw Error('disposable snapshot only')
const file='kernel/model-values.ts',text=readFileSync(file,'utf8'),anchor="return [...terms].slice(0, 16).map(value => ({op: 'const', value}))"
if(!text.includes(anchor))throw Error('source mismatch')
writeFileSync(file,text.replace(anchor,'return []'))
