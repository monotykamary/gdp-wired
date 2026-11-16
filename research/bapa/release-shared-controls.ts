// Data-only fresh Lean project for accepted shared bridge/control modules.
import {readFileSync, writeFileSync, mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {leanProject} from '../../lean-kernel/emit.ts'
const out=process.argv[2]
if(!out)throw Error('usage: release-shared-controls.ts NEW_PROJECT')
const body=`import FiniteSimulationControls
import PaxosEprScanSimulation
import TypedBoundControls
import SourceInclusionControls
import RadixCertificateTransport
#print axioms Bapa.FiniteSimulationControls.unreproducible_propose_refused
`
const project=leanProject(body,{name:'ReleaseControls'})
for(const name of ['CertificateBoundErasure','CertificateBoundSubstitution','CertificateBooleanCleanup','BoundErasureReplay','CountedSourceProjection','CountedNoninterference','CountedSourceBridge','SourceInclusion','SourceInclusionControls','FiniteSimulation','FiniteSimulationControls','PaxosEprScanSimulation','TypedBoundControls','RadixKeySyntax','RadixBinderExpansion','RadixCertificateTable','RadixTupleSyntax','RadixEqualityTree','RadixCertificateTransport'])project[name+'.lean']=readFileSync(new URL('./'+name+'.lean',import.meta.url),'utf8')
const modules=Object.keys(project).filter(n=>n.endsWith('.lean')&&n!=='lakefile.lean').map(n=>n.slice(0,-5))
project['lakefile.lean']='import Lake\nopen Lake DSL\npackage releasecontrols\n@[default_target]\nlean_lib ReleaseShared where\n  roots := #['+modules.map(n=>'`'+n).join(', ')+']\n'
mkdirSync(out)
for(const [name,text]of Object.entries(project))writeFileSync(join(out,name),text,{flag:'wx'})
console.log(JSON.stringify({status:'EMITTED_NOT_CHECKED',newProtocolSearches:0,modules}))
