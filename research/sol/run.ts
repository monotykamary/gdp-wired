// The Solidity front end on one file, everything it says: refusals, notes, the rule printed, the check's evidence.
//   bun research/sol/run.ts <file.sol> [entry] [--root dir]
import {extractSolidity} from '../../core/extract-sol.ts'
const [file, entry] = process.argv.slice(2).filter(a => !a.startsWith('--'))
const root = process.argv.includes('--root') ? process.argv[process.argv.indexOf('--root') + 1] : undefined
const x = extractSolidity(file!, {...(entry ? {entry} : {}), ...(root ? {root} : {})})
console.log(JSON.stringify({ok: x.ok, refusals: x.refusals, notes: x.notes, evidence: x.evidence}, null, 1))
if (x.source) console.log(x.source)
