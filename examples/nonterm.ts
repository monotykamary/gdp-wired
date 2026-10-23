// Runs that never end: proveNeverEnds, the claim a halting proof refutes. Each loop here has a run that goes on
// forever, found and checked (a closed recurrent set with the turn from each of its states given, a start and a stem
// into it), beside its twin that halts, which proveLoop proves and proveNeverEnds can't.
//   bun examples/nonterm.ts
import {bool, count, loop, min, nat, proveLoop, proveNeverEnds, upTo, when, yes} from '../core/dsl.ts'

// Pagination where a page may be empty: a server that keeps sending empty pages keeps the client asking forever. Its
// twin asks for pages of at least one item, and halts (rank total − cur).
export const pagesMayBeEmpty = loop('pagination, empty pages allowed').params({total: nat}).inputs({page: nat}).state({cur: 0})
  .while(({cur, total}) => cur.lt(total)).body(({cur, page, total}) => ({cur: cur.plus(min(page, total.minus(cur)))}))
export const pagesNonEmpty = loop('pagination, pages of one item or more').params({total: nat}).inputs({page: nat}).state({cur: 0})
  .while(({cur, total}) => cur.lt(total)).assume(({page}) => page.atLeast(1)).body(({cur, page, total}) => ({cur: cur.plus(min(page, total.minus(cur)))}))
  .rank(({total, cur}) => total.minus(cur))

// A retry loop with no cap: while the call fails it waits and tries again, the wait growing to its ceiling. A service
// that never answers keeps it going; its twin gives up after `tries` attempts.
export const retryForever = loop('retry with no cap').params({ceiling: nat}).inputs({ok: bool}).state({done: 0, wait: 1})
  .while(({done}) => done.lt(1)).body(({ok, wait, ceiling}) => ({done: count(ok), wait: min(wait.plus(wait), ceiling)}))
export const retryCapped = loop('retry with a cap').params({ceiling: nat, tries: nat}).inputs({ok: bool}).state({done: 0, n: 0, wait: 1})
  .while(({done, n, tries}) => done.lt(1).and(n.lt(tries))).body(({ok, n, wait, ceiling}) => ({done: count(ok), n: n.plus(1), wait: min(wait.plus(wait), ceiling)}))
  .rank(({tries, n}) => tries.minus(n))

// A ring buffer's reader that never stops: its index wraps at the size, so the run comes back (a lasso). Its twin reads
// each slot once.
export const ringReader = loop('ring reader').params({size: upTo(8)}).state({i: 0}).pre(({size}) => size.atLeast(1))
  .while(() => yes).body(({i, size}) => ({i: when(i.plus(1).atLeast(size), 0, i.plus(1))}))
export const sweepOnce = loop('sweep once').params({size: upTo(8)}).state({i: 0}).while(({i, size}) => i.lt(size)).body(({i}) => ({i: i.plus(1)})).rank(({size, i}) => size.minus(i))

if (import.meta.main) {
  const twins: [Parameters<typeof proveLoop>[0], Parameters<typeof proveLoop>[0]][] = [[pagesMayBeEmpty, pagesNonEmpty], [retryForever, retryCapped], [ringReader, sweepOnce]]
  for (const [never, halts] of twins) {
    const n = proveNeverEnds(never, {ms: 5000}), h = proveLoop(halts, [])
    console.log(`${never.loop.name}: never ends ${n.proven && n.checked} (${n.by}, a stem of ${n.recur?.stem.length} turns); ${halts.loop.name}: halts ${h.proven && h.checked}, never ends ${proveNeverEnds(halts, {ms: 1000}).proven}`)
  }
}
