// GIVEN-seed diagnostic export, including a checked original-source wrapper.
// This is not automatic discovery or naive-consensus port acceptance.
import {writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {toLean} from '../../lean-kernel/emit.ts'
import {proveLaws} from '../../kernel/prove.ts'
import {rigidMinimalWrapper} from './rigid-minimal-wrapper.ts'
import {rigidMinimalGivenZero, rigidMinimalLaw} from './rigid-minimal.ts'
const out = process.env.SUPERCOMPUTER_OUTPUT_DIR!
const {abstractMachine: machine, instancePrecondition} = rigidMinimalGivenZero()
const report = proveLaws(machine, [rigidMinimalLaw])
writeFileSync(join(out, 'minimal-report.json'), JSON.stringify({report, searchSeed: 'GIVEN intersection instance at (0,0)', seedFound: false, acceptance: false}, null, 2)+'\n')
if (!report.proven || !report.checked) throw Error('minimal rigid law did not close')
const choice = Object.keys(machine.fns!).find(n => n !== 'member')!
const text = toLean([{id: 'rigid_minimal', machine, laws: [rigidMinimalLaw], lean: {after: ix => rigidMinimalWrapper(machine, choice, ix)}}], {native: false, cyclic: false})
writeFileSync(join(out, 'RigidMinimalGenerated.lean'), text.replace('import History', 'import RigidEncoding\nimport History'))
writeFileSync(join(out, 'minimal-machine.json'), JSON.stringify({machine, laws: [rigidMinimalLaw], instancePrecondition}, null, 2)+'\n')
