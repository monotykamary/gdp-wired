// One source's struct and methods through the Go front end, its refusals and evidence printed (a diagnostic).
//   bun research/extract/go-one.ts <repo> <commit> <dir> <Type> <m1,m2> [discard]
import {extractGo} from '../../core/extract-go.ts'
import {checkout} from './go-fetch.ts'
const [repo, commit, dir, entry, ms, mode] = process.argv.slice(2)
const x = extractGo(checkout(repo!, commit!, dir!), {entry: entry!, methods: ms!.split(','), ...(mode === 'discard' ? {onError: 'discard' as const} : {}), check: {runs: 40, depth: 8, states: 80}})
console.log(JSON.stringify({ok: x.ok, refusals: x.refusals, evidence: x.evidence}))
