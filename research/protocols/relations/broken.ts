// The broken variant of a port through proveRule with the search, the full stack of any error.
//   bun research/protocols/relations/broken.ts <id>
import {proveRule} from '../../../core/dsl.ts'
import {protocols} from '../ic3syn/models.ts'
const p = protocols.find(q => q.id === process.argv[2])!, bad: any = p.make(p.bug)
Error.stackTraceLimit = 80
try { const v: any = proveRule(bad, p.laws(bad), {search: {ms: 60000}}); console.log(JSON.stringify({verdict: v.proven ? 'proven' : v.run ? 'refuted' : 'unknown', goal: v.goal})) }
catch (e) { console.log((e as Error).stack) }
