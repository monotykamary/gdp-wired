// Sizes of sets over a universe of names (dsl.ts's within, sizeBelow): the team roster of examples/sizes.ts proven and its
// broken variant refused; on random runs the size term is the number of names in the set, every law holds, and the
// broken variant is broken by a run.
import {expect, test} from 'bun:test'
import {evalE, interpret} from './machine.ts'
import {NAMES, team, teamLaws, teamSteps} from '../examples/sizes.ts'
import {proveLaws, proveStepLaws} from '../kernel/prove.ts'
import {allowed, watch} from './watch.ts'

test('the team roster: proven; checking the current team instead refused', () => {
  expect(proveStepLaws(team().machine, teamLaws(), teamSteps())).toMatchObject({proven: true, checked: true})
  const bad = team('checks the current team')
  expect(proveLaws(bad.machine, teamLaws(bad)).proven).toBe(false)
})

test('runs: the size is the count of names; every law holds, and the broken variant breaks one', () => {
  let seed = 13
  const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
  const size = team().law('size', ({Team}) => Team.sizeBelow(NAMES).atLeast(0)).holds as {b: Parameters<typeof evalE>[0]}
  for (const bug of [undefined, 'checks the current team'] as const) {
    const r = team(bug), m = r.machine, run = interpret(m), laws = [...teamLaws(r), ...(bug ? [] : teamSteps(r))]
    let broken = false
    for (let t = 0; t < 300 && !broken; t++) {
      const params = {cap: rand(4)}
      let st = run.init(params)
      const on = laws.map(l => watch(m, run, l, params, NAMES))
      for (let i = 0; i < 6; i++) {
        // Rosters mostly within the universe, now and then a name past it.
        const names = [0, 1, 2, 3, 4].filter(n => rand(n === 4 ? 6 : 2) === 0)
        const input = r.encodeInput({Roster: names})
        if (!allowed(m, run, params, st, input)) continue
        const before = st
        st = run.step(params, st, input)
        const members = [...st.maps.Team!.entries()].filter(([, v]) => v === 1).length
        if (!bug) expect(evalE(size.b, params, st, m)).toBe(members)
        if (!on.every(w => w.step(before, input, st))) broken = true
      }
    }
    expect(broken).toBe(bug !== undefined)
  }
})
