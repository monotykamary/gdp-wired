// The search keeps its end on the wall (kernel/prove.ts's withWall): two protocols whose searches ran far past it
// (wo_decide's caller goal, ring's model checks) with tight budgets end within the budget and half a second, beyond what
// the same call takes with a search of 0 ms (the prover's own proof and the deeper runs before the search's clock starts).
// And the enumeration's two caller goals that ran past it (callers/: ring's 'one leader' with 33 cubes assumed, 300 s
// in the function parts' congruence; wo_decide's with 36), proveLaw alone inside a wall of 2, 5 and 10 s.
//   bun test research/protocols/epr/deadline.test.ts
import {readFileSync} from 'node:fs'
import {expect, test} from 'bun:test'
import {proveRule} from '../../../core/dsl.ts'
import {decideLaw, proveLaw, withWall} from '../../../kernel/prove.ts'
import {protocols} from '../models.ts'

// (wo_decide from 5 s: its search's runs, core/infer.ts's 16,000 requests, take 1.4 s of wall time at any budget)
// (sharded KV's: its search's last bounded runs within the search's end, not 18 s past it)
for (const [id, budgets] of [['consensus_wo_decide', [5_000, 10_000]], ['ring_leader_election', [2_000, 5_000]], ['sharded_key_value_store', [5_000, 10_000]]] as const) {
  for (const ms of budgets) {
    test(`${id}: a ${ms} ms search ends in time`, () => {
      const p = protocols.find(q => q.id === id)!, r = p.make(), laws = p.laws(r)
      const t0 = performance.now()
      proveRule(r, laws, {search: {ms: 0}})
      const base = performance.now() - t0, t1 = performance.now()
      const v = proveRule(r, laws, {search: {ms}})
      const took = performance.now() - t1
      console.log(JSON.stringify({id, ms, base: Math.round(base), took: Math.round(took), verdict: v.proven ? 'proven' : v.stuck ?? 'unknown'}))
      expect(took).toBeLessThan(base + ms + 500)
    }, 600_000)
  }
}

for (const id of ['ring', 'cons']) {
  for (const ms of [2_000, 5_000, 10_000]) {
    test(`${id}'s caller goal, cubes assumed: proveLaw ends ${ms} ms in`, () => {
      const {m, laws, i} = JSON.parse(readFileSync(`${import.meta.dir}/callers/${id}.json`, 'utf8'))
      const t = performance.now(), r = withWall(performance.now() + ms, () => proveLaw(m, laws, i)), took = performance.now() - t
      console.log(JSON.stringify({id, ms, took: Math.round(took), out: r.proven ? 'proven' : r.stuck}))
      expect(took).toBeLessThan(ms + 500)
    }, 60_000)
  }
}

// The enumeration's unsure cube goals (callers/<p>-cubes.json: gen/enum4's first Houdini round, 13 of ring's and 21 of
// distributed_lock's, each 2 s of CDCL and 2 s of proof there): decideLaw decides each, a model, as Z3 4.13 does on their
// step goals (research/protocols/epr/DESIGN.md, gen/epr5), within a second.
for (const p of ['ring', 'dist']) {
  test(`${p}'s unsure cubes: decideLaw finds each one's model`, () => {
    const {m, laws, unsure} = JSON.parse(readFileSync(`${import.meta.dir}/callers/${p}-cubes.json`, 'utf8'))
    for (const i of unsure as number[]) {
      const t = performance.now(), r = withWall(performance.now() + 2_000, () => decideLaw(m, laws, i)), took = performance.now() - t
      console.log(JSON.stringify({p, i, took: Math.round(took), out: r === undefined ? 'unknown' : r.proven ? 'proven' : r.stuck}))
      expect(r && !r.proven ? r.stuck : r).toBe('sat')
      expect(took).toBeLessThan(1_000)
    }
  }, 120_000)
}
