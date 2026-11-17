// A deliberately limited printing/API check. This is NOT a machine-law gate:
// it checks only descriptors, fixed helper dispatch, and namespace preservation.
import {writeFileSync} from 'node:fs'
import {generateGenericWordGate} from './generic-lean-gate.ts'
const id = 'generic_q64'
const full = generateGenericWordGate([id]).source
const marker = `theorem ${id}_word_extra_sound`
const at = full.indexOf(marker)
if (at < 0) throw Error('missing descriptor prefix')
const source = full.slice(0, at) + `\n#print axioms ${id}_word_spec0_values\n#print axioms ${id}_word_spec0_reserved\n`
const target = process.argv[2]
if (!target) throw Error('descriptor preflight needs output path')
writeFileSync(target, source)
console.log(JSON.stringify({descriptorOnly: true, machineLawsChecked: false, target}))
