import {protocols} from '../protocols/ic3syn/models.ts'
import {quorumLaws} from '../../core/quorum-laws.ts'
import {fieldLaws} from '../../core/field-laws.ts'
const rows = protocols.map(p => {
  const m = p.make().machine, t = performance.now(), quorum = quorumLaws(m)
  return {id: p.id, quorumLaws: quorum.laws.length, quorumCounts: Object.keys(quorum.counts).length, composedFieldLaws: fieldLaws(m).length - fieldLaws(m, false).length, ms: performance.now() - t}
})
console.log(JSON.stringify(rows))
if (rows.filter(r => r.quorumLaws || r.composedFieldLaws).length !== 1 || !rows.find(r => r.id === 'mldr')?.quorumLaws) throw Error('unexpected additional structural trigger')
