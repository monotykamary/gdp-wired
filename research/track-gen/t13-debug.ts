import {protocols} from '../protocols/ic3syn/models.ts'
import {quorumLaws} from '../../core/quorum-laws.ts'
import {fieldLaws} from '../../core/field-laws.ts'
import {trueSmall} from '../../core/exists.ts'
const m = protocols.find(p => p.id === 'mldr')!.make().machine, g = quorumLaws(m), mm = {...m, counts: {...m.counts, ...g.counts}}
console.log(JSON.stringify(g))
for (const law of [...g.laws, ...fieldLaws(mm).filter(l => l.name.endsWith('rows agree'))]) {
 const t = performance.now(); console.log(JSON.stringify({name:law.name,kept:trueSmall(mm,[law]),ms:performance.now()-t}))
}
