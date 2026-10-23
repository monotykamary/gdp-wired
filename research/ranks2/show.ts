// Dev: an ARI task's rules in one line each. `bun research/ranks2/show.ts <task.ari>`
import {readFileSync} from 'node:fs'
import {parseAri, type Sx} from '../../compare/term/ari.ts'
const t = parseAri(readFileSync(process.argv[2]!, 'utf8'))
const sx = (s: Sx): string => (typeof s === 'string' ? s : `(${s.map(sx).join(' ')})`)
console.log('entry', t.entry, t.funs.size, 'locations')
for (const r of t.rules) console.log(r.from, r.lhs.map(sx).join(' '), '->', r.to, r.rhs.map(sx).join(' '), ':', sx(r.guard))
