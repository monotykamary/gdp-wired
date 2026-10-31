// The Solidity front end on one file, everything it says: refusals, notes, the rule printed, the check's evidence.
//   bun research/sol/run.ts <file.sol> [entry] [--root dir]
import {extractSolidity} from '../../core/extract-sol.ts'
const argv = process.argv.slice(2), [file, entry] = argv.filter((a, i) => !a.startsWith('--') && argv[i - 1] !== '--root')
const root = process.argv.includes('--root') ? process.argv[process.argv.indexOf('--root') + 1] : undefined
const quick = process.argv.includes('--quick'), t0 = performance.now()
const x = extractSolidity(file!, {...(entry ? {entry} : {}), ...(root ? {root} : {}), ...(quick ? {check: {runs: 10, states: 20, probes: process.argv.includes('--probes')}} : {})})
console.error(`extracted in ${Math.round(performance.now() - t0)} ms`)
console.log(JSON.stringify({ok: x.ok, refusals: x.refusals, notes: x.notes, evidence: x.evidence}, null, 1))
if (x.source) console.log(x.source)
