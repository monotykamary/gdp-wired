// Minimal reproduction of stale fresh-binder instances in the untrusted memo.
// No sized sort, tuple relation, count, helper or BAPA kernel extension is used.
// Compare: bun this-file.ts; GDP_MEMO_ALPHA=0 bun this-file.ts.
import {bool, nat, no, rule} from '../../core/dsl.ts'
import {checkLaws} from '../../kernel/kernel.ts'
import {proveLaws, proveSetFast} from '../../kernel/prove.ts'
const make = () => rule('fresh binder memo reproduction')
  .inputs({i: nat}).maps({Flag: bool.from(false)})
  .step(({i, Flag}) => ({Flag: Flag.set(i, no)}))
const a = make(), first = proveSetFast(a.machine, a.kindLaws())
const b = make(), laws = b.kindLaws(), fast = proveSetFast(b.machine, laws)
const ordinary = proveLaws(b.machine, laws)
console.log(JSON.stringify({
  alpha: process.env.GDP_MEMO_ALPHA ?? 'default',
  first: {proven: first.proven, checked: first.checked},
  fast: {proven: fast.proven, checked: fast.checked, failed: fast.failed},
  ordinary: {proven: ordinary.proven, checked: ordinary.checked, rechecked: !!ordinary.proof && checkLaws(b.machine, laws, ordinary.proof)},
}, null, 2))
