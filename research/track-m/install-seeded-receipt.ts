// Portable metadata capture only; no additional proof fact or changed checker.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux required')
const path='core/count-recovery/conditional-proof.ts',before=readFileSync(path,'utf8'),anchor='  marked.set(tree, {goal, lemmas})'
if(before.split(anchor).length!==2)throw Error('conditional mark anchor')
const after="import {lemmaRecorder as __l} from '../../research/track-m/section18-recorder.ts'\n"+before.replace(anchor,anchor+';__l.noteMark(tree,{goal,lemmas})')
writeFileSync(path,after)
console.log(JSON.stringify({observationOnly:true,path,before:createHash('sha256').update(before).digest('hex'),after:createHash('sha256').update(after).digest('hex')}))
