import {writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {checkLaws} from '../../kernel/kernel.ts'
import {proveLaws} from '../../kernel/prove.ts'
import {toLean} from '../../lean-kernel/emit.ts'
import {lockServerSized, lockServerSizedLaws, lockServerUnrestrictedLaws} from './lock-server-sized.ts'
const r = lockServerSized(), machine = r.machine
if (machine.counts || machine.sums) throw new Error('the migration must be uncounted')
const items = [
  {id: 'lock_server_sized', machine, laws: [...r.kindLaws(), ...lockServerSizedLaws(r)]},
  {id: 'lock_server_unrestricted', machine, laws: [...r.kindLaws(), ...lockServerUnrestrictedLaws(r)]},
]
const out = process.env.SUPERCOMPUTER_OUTPUT_DIR!
const reports = items.map(item => {
  const report = proveLaws(machine, item.laws)
  if (!report.proven || !report.checked || !report.proof || !checkLaws(machine, item.laws, report.proof)) throw new Error(`${item.id}: no ordinary checked proof`)
  return {...item, report, label: 'helper given, not found'}
})
writeFileSync(join(out, 'proof.json'), JSON.stringify(reports, null, 2) + '\n')
writeFileSync(join(out, 'LockServerSized.lean'), toLean(items, {native: false, cyclic: false}))
