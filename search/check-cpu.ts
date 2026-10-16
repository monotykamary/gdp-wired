// The JS twin of the kernel against the interpreter, on random candidates of every search.
import {NONE, js, replay, size} from './compile.ts'
import {searches} from './models.ts'
for (const s of searches) {
  const f = js(s.m, s.law, s.space), total = size(s.m, s.space)
  let agree = 0, failing = 0
  for (let t = 0; t < 20000; t++) {
    const index = Math.floor(Math.random() * total)
    const got = f(index), want = replay(s.m, s.law, s.space, index)
    if ((got === NONE) === (want === undefined) && (want === undefined || want.trace.length === got)) agree++
    if (want) failing++
  }
  console.log(`${s.what.padEnd(34)} ${total.toLocaleString().padStart(14)} candidates; 20000 sampled: ${agree} agree (${failing} fail the law)`)
}
