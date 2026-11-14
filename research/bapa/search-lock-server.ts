// A separate diagnostic: ONLY the original safety law supplied, no helper.
// This is not a canonical-profile run or a measurement claim.
import {writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {proveRule} from '../../core/dsl.ts'
import {lockServerSized, lockServerSizedLaws} from './lock-server-sized.ts'
const r = lockServerSized(), safety = lockServerSizedLaws(r)[0]!
if (r.machine.counts || r.machine.sums) throw new Error('search must remain uncounted')
const ms = Number(process.env.BAPA_SEARCH_MS ?? 5_000)
if (![5_000, 60_000, 600_000].includes(ms)) throw new Error('unexpected search budget')
const started = performance.now()
const verdict = proveRule(r, [safety], {search: {ms}})
const elapsedMs = performance.now() - started
writeFileSync(join(process.env.SUPERCOMPUTER_OUTPUT_DIR!, 'helper-search.json'), JSON.stringify({
  label: 'no-given-helper uncounted search, not canonical profile',
  requestedSearchMs: ms, elapsedMs,
  suppliedLaws: [safety], verdict,
}, null, 2) + '\n')
