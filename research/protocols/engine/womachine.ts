// gen/wo: wo's machine and the EPR patterns its written laws give (a look, no search)
import {patternsOf} from '../../../kernel/epr.ts'
import {protocols} from '../models.ts'
const p = protocols.find(q => q.id === 'consensus_wo_decide')!, r: any = p.make(), m = r.machine
console.log(JSON.stringify({inputs: m.inputs, inputMaps: m.inputMaps, assume: m.assume, flags: m.step.flags, maps: m.step.maps?.VotingQuorum}, null, 0).slice(0, 4000))
console.log(JSON.stringify(patternsOf(m, [...r.kindLaws(), ...p.human(r), ...p.laws(r)])))
