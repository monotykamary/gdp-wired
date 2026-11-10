// Step 0 diagnostic: where the original capture spends time before its first query.
import {protocols} from '../protocols/ic3syn/models.ts'
import {smallOf} from '../../core/exists.ts'
import {candidates, guardLaws} from '../../core/counts.ts'
import {clock} from '../../kernel/prove.ts'
const p = protocols.find(p => p.id === 'mldr')!, r = p.make(), m = r.machine
const t = performance.now()
console.log('before smallOf')
console.log(JSON.stringify({samples: smallOf(m).map(s => s.sts.length), ms: performance.now() - t}))
const g = guardLaws(m), caller = [...r.kindLaws(), ...p.laws(r)]
console.log('before candidates')
const found = candidates(m, m, caller, caller, g.laws, 60_000, clock() + 60_000)
console.log(JSON.stringify({candidates: found.map(l => l.name), ms: performance.now() - t}))
