// gdp-wired/lean end to end: rules written with the builders, exported by toLean, laid out by leanProject, and built by
// `lake build` (modal/suite.json's lean-package job). Usage: bun package-check.ts <empty folder>
import {mkdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {bool, count, forall, loop, maybe, min, nat, oneOf, relation, rule, yes} from '../core/dsl.ts'
import {escrowLaws, escrowSteps, escrowWatched} from '../examples/composition.ts'
import {leanProject, toLean} from './emit.ts'

const caps = rule('caps').params({d: nat}).inputs({acct: nat, day: nat, ok: bool}).maps({Acct: 0, Day: 0})
  .flags(({ok, acct, day, d, Acct, Day}) => ({granted: ok.and(Acct.at(acct).lt(1), Day.at(day).lt(d))}))
  .step(({acct, day, granted, Acct, Day}) => ({Acct: Acct.bump(acct, granted), Day: Day.bump(day, granted)}))
const dayCap = caps.law('day cap', ({Day, d}) => forall(k => Day.at(k).atMost(d)))
const onlyUp = caps.stepLaw('no count goes down', ({Day}, after) => forall(k => Day.at(k).atMost(after.Day.at(k))))
const twice = caps.stepsLaw('two grants on one day add two', 2, ({day, Day}, after, [, next]) => next!.day.eq(day).implies(after.Day.at(day).eq(Day.at(day).plus(2))), ({granted}) => granted)
const window = rule('window limit').params({w: nat, c: nat, now: nat}).inputs({forced: bool, t: nat}).log('forced', 't')
  .sums({ours: (r, {now, w}) => count(r.forced.not().and(r.t.atMost(now), now.lt(r.t.plus(w))))})
  .queries({seen: (r, {t, w}) => count(t.lt(r.t.plus(w)))})
  .flags(({forced, seen, c}) => ({admitted: forced.not().and(seen.plus(1).atMost(c))}))
  .keep(({forced, admitted}) => forced.or(admitted))
  .relations(({t, now, ours, seen}) => [relation(ours.atMost(seen), t.atMost(now))])
const trial = rule('trial').inputs({plan: oneOf('free', 'pro'), spent: maybe(nat), allowance: maybe(nat)})
const failsClosed = trial.decide('a missing fact means no trial', ({spent}) => spent.isNone,
  ({plan, spent, allowance}) => plan.match({free: () => spent.match({none: () => yes, some: s => allowance.match({none: () => yes, some: a => s.atLeast(a)})}), pro: () => yes}))
const pages = loop('pagination').params({total: nat}).inputs({page: nat}).state({cur: 0}).while(({cur, total}) => cur.lt(total))
  .assume(({page}) => page.atLeast(1)).body(({cur, page, total}) => ({cur: cur.plus(min(page, total.minus(cur)))})).rank(({total, cur}) => total.minus(cur))

const file = toLean([
  {id: 'caps', machine: caps.machine, laws: [dayCap], stepLaws: [onlyUp, twice]},
  {id: 'window', machine: window.machine, laws: [window.law('window ceiling', ({ours, c}) => ours.atMost(c))]},
  {id: 'trial', goal: failsClosed.goal},
  {id: 'pages', loop: pages.loop, rank: pages.rankTerms},
  {id: 'escrow', machine: escrowWatched(), laws: escrowLaws, stepLaws: escrowSteps},
], {title: 'gdp-wired/lean, end to end'})
const out = process.argv[2]
if (!out) throw new Error('usage: bun package-check.ts <empty folder>')
mkdirSync(out, {recursive: true})
for (const [name, text] of Object.entries(leanProject(file))) writeFileSync(join(out, name), text)
console.log(`${Object.keys(leanProject(file)).length} files in ${out}; ${[...file.matchAll(/^theorem /gm)].length} theorems`)
