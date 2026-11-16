import {mkdirSync,writeFileSync,rmSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {protocols} from '../../research/protocols/ic3syn/models.ts'
import {spawnSync} from 'node:child_process'
import {leanProject} from '../emit.ts'
import {leanLibrary} from '../library.ts'
import {leanSource} from '../lift/project.ts'
const out=process.env.SUPERCOMPUTER_OUTPUT_DIR
if(!out)throw Error('remote output directory required')
const dir=join(out,'project');mkdirSync(dir)
const p=Object.assign(leanProject('import InvariantSimulation\nimport SemanticSums\nimport RadixSumTransport\n',{name:'SimulationCheck'}),leanLibrary)
const fixture=protocols.find(p=>p.id==='simple_decentralized_lock')!
const rule=fixture.make()
const source=JSON.stringify({schema:'gdp-lift-source/v1',id:fixture.id,machine:rule.machine,laws:fixture.laws(rule)},null,2)+'\n'
writeFileSync(join(out,'source.json'),source)
writeFileSync(join(out,'source.sha256'),createHash('sha256').update(source).digest('hex')+'\n')
for(const n of ['InvariantSimulation','SemanticSums','RadixSumTransport'])p[n+'.lean']=leanSource(n)
const modules=Object.keys(p).filter(n=>n.endsWith('.lean')&&n!=='lakefile.lean').map(n=>n.slice(0,-5))
p['lakefile.lean']='import Lake\nopen Lake DSL\npackage simulationcheck\n@[default_target]\nlean_lib SimulationCheck where\n  roots := #['+modules.map(n=>'`'+n).join(', ')+']\n'
for(const [n,s]of Object.entries(p))writeFileSync(join(dir,n),s)
const r=spawnSync('lake',['build'],{cwd:dir,encoding:'utf8',timeout:900000,maxBuffer:16000000})
writeFileSync(join(out,'lean.log'),(r.stdout??'')+(r.stderr??''))
rmSync(join(dir,'.lake'),{recursive:true,force:true})
if(r.error||r.status!==0)throw Error('native lemma check failed: '+String(r.error??r.status))
