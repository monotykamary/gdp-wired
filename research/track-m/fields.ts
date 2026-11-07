import {fieldLaws} from '../../core/field-laws.ts'
import {holdsAt, smallOf, trueSmall} from '../../core/exists.ts'
import {protocols} from '../protocols/ic3syn/models.ts'
const p = protocols.find(p => p.id === 'mldr')!, r = p.make(), m = r.machine
const start = performance.now(), states = smallOf(m), laws = fieldLaws(m), kept = laws.filter(l => trueSmall(m, [l]))
console.log(JSON.stringify({samples: states.map(s => s.sts.length), proposed: laws.length, kept: kept.map(l => l.name), ms: performance.now() - start}))
for (const law of laws.filter(l => !kept.includes(l))) {
  for (const {p, sts} of states) {
    const s = sts.find(s => !holdsAt(m, law, p, s, 4))
    if (s) { console.log(JSON.stringify({rejected: law.name, p, scalars: s.scalars})); break }
  }
}
