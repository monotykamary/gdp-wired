// TEST-ONLY fixture export. The production generator has no source registry.
// Calling constructors/laws constructs ASTs; this script never invokes proof,
// protocol search, certificate replay, or retained Lean code.
import {writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {protocols} from '../../research/protocols/ic3syn/models.ts'
const p=protocols.find(p=>p.id==='toy_consensus_forall')!
const r=p.make()
const source={schema:'gdp-lift-source/v1',id:p.id,machine:r.machine,laws:p.laws(r)}
const text=JSON.stringify(source,null,2)+'\n'
writeFileSync(process.argv[2]!,text,{flag:'wx'})
console.log(JSON.stringify({path:process.argv[2],sha256:createHash('sha256').update(text).digest('hex')}))
