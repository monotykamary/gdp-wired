// Dev: why relationOf refuses a task. `bun research/ranks2/rel.ts <task.ari>`
import {readFileSync} from 'node:fs'
import {parseAri} from '../../compare/term/ari.ts'
import {build} from '../../compare/term/translate.ts'
import {relationOf} from '../../core/relation.ts'
const b = build(parseAri(readFileSync(process.argv[2]!, 'utf8')), 'task')
const t = performance.now()
for (const cap of [4000, 20000, 100000]) { const r = relationOf(b.loop, [], cap); console.log(cap, r ? `${r.paths.length} paths` : 'refused', Math.round(performance.now() - t), 'ms') }
