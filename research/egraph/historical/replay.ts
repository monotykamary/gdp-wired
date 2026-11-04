import {readFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {type Cyclic,refuseCyclic} from '../../../kernel/cyclic.ts'
const file=process.argv[2];if(!file)throw Error('proof file required')
const bytes=readFileSync(file),proof=JSON.parse(bytes.toString()) as Cyclic
const reason=refuseCyclic(proof)
console.log('FRESH_REPLAY',JSON.stringify({file,sha256:createHash('sha256').update(bytes).digest('hex'),nodes:proof.nodes.length,rootUses:proof.nodes.at(-1)?.uses.length,checked:reason===undefined,reason}))
if(reason!==undefined)process.exitCode=1
