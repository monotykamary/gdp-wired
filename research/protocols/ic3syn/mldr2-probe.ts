// The kernel check of a candidate inductive set for mldr, on either port (design experiment, MLDR-DESIGN.md): the set
// written whole as laws over counts, searchCounted with GDP_COUNTS_GIVEN=1 (the callers alone, no candidate) so the
// verdict is whether the set as given goes through the counted kernel. GDP_COUNTS_TRACE=123 shows each attempt.
//   GDP_COUNTS_GIVEN=1 GDP_COUNTS_TRACE=123 bun research/protocols/ic3syn/mldr2-probe.ts <cur|pstar> <star|3246> [ms]
import {protocols} from './models.ts'
import {type C, type E, type Law, type Machine, all, any, atMost, get, ite, less, minus, n, not, plus, same, times, x} from '../../../core/machine.ts'
import {countsDump, searchCounted} from '../../../core/counts.ts'
import {mkdirSync, writeFileSync} from 'node:fs'

export function mldrHandSet(inv = 'star', overlap: 'half' | 'uw' = 'half') {
const N = 64
const p = protocols.find(q => q.id === 'mldr')!, r: any = p.make(), m0: Machine = r.machine
const one = n(1), zero = n(0), two = (e: E) => times(2, e), ind = (c: C): E => ite(c, one, zero)
const at = (c: string, a: string, b?: string): E => get(c, b ? plus(times(N, x(a)), x(b)) : x(a))
const cfg = (s: E, k: E): C => same(get('Config', plus(times(N, s), k)), one)
const newer = (a: E, b: E): C => any(less(get('CfgT', b), get('CfgT', a)), all(same(get('CfgT', a), get('CfgT', b)), less(get('CV', b), get('CV', a))))
const counts: Machine['counts'] = {
  ...m0.counts,
  // |config[s]|; |{k ∈ config[s] : ¬newer(k, s)}| (ConfigDisabled(s) is 2·old[s] ≤ cfgSize[s])
  cfgSize: {j: 'cj', key: 'ck', below: x('size'), body: ind(cfg(x('cj'), x('ck')))},
  old: {j: 'oj', key: 'ok', below: x('size'), body: ind(all(cfg(x('oj'), x('ok')), not(newer(x('ok'), x('oj')))))},
  // at N·s + t: |config[s] \ config[t]|, |config[s] ∩ config[t]|
  xm: {j: 'mj', lo: 'ml', base: N, key: 'mk', below: x('size'), body: ind(all(cfg(x('mj'), x('mk')), not(cfg(x('ml'), x('mk')))))},
  xn: {j: 'nj', lo: 'nl', base: N, key: 'nk', below: x('size'), body: ind(all(cfg(x('nj'), x('nk')), cfg(x('nl'), x('nk'))))},
  ...(inv === 'star'
    // at N·a + j: |{k ∈ config[a] : CT[k] < CfgT[j] ∧ ¬newer(k, a)}|: the members that could still vote for a leader of config a in term CfgT[j]
    ? {bq: {j: 'bj', lo: 'bl', base: N, key: 'bk', below: x('size'), body: ind(all(cfg(x('bj'), x('bk')), less(get('CT', x('bk')), get('CfgT', x('bl'))), not(newer(x('bk'), x('bj')))))}}
    // at N·a + j: |{k ∈ config[a] : CT[k] < CfgT[j]}|
    : {low: {j: 'lj', lo: 'll', base: N, key: 'lk', below: x('size'), body: ind(all(cfg(x('lj'), x('lk')), less(get('CT', x('lk')), get('CfgT', x('ll')))))}}),
}
const m: Machine = {...m0, counts}
const sz = (v: string): C => less(x(v), x('size'))
const unstarted = same(x('started'), zero)
const is = (mp: string, a: string, v: number): C => same(get(mp, x(a)), n(v))
const disabled = (i: string): C => atMost(two(at('old', i)), at('cfgSize', i))
const law = (name: string, forall: string, keys: string[], hyps: C[], then: C | C[]): Law => ({name, forall, keys, holds: any(not(all(...hyps)), ...(Array.isArray(then) ? [all(...then)] : [then]))})
const laws: Law[] = [
  ...p.laws(r),
  law('Inv866: a primary at its config term', 'a$', [], [sz('a$'), is('St', 'a$', 1)], same(get('CfgT', x('a$')), get('CT', x('a$')))),
  law('Inv3915: one config term, the primary newest', 'a$', ['b$'], [sz('a$'), sz('b$'), same(get('CfgT', x('a$')), get('CfgT', x('b$'))), is('St', 'a$', 1)], not(newer(x('b$'), x('a$')))),
  law('Inv1758: one version and term, one config', 'a$', ['b$', 'c$'], [sz('a$'), sz('b$'), sz('c$'), same(get('CV', x('a$')), get('CV', x('b$'))), same(get('CfgT', x('a$')), get('CfgT', x('b$')))],
    same(get('Config', plus(times(N, x('a$')), x('c$'))), get('Config', plus(times(N, x('b$')), x('c$'))))),
  overlap === 'half' ? {name: 'Inv2973: quorums overlap, or a config disabled', forall: 'a$', keys: ['b$', 'u$', 'w$'], holds: any(
    not(all(sz('a$'), sz('b$'), atMost(two(x('u$')), at('cfgSize', 'a$')), less(at('cfgSize', 'a$'), plus(two(x('u$')), n(2))), atMost(two(x('w$')), at('cfgSize', 'b$')), less(at('cfgSize', 'b$'), plus(two(x('w$')), n(2))))),
    disabled('a$'), disabled('b$'), less(at('xn', 'a$', 'b$'), plus(minus(plus(x('u$'), one), at('xm', 'a$', 'b$')), minus(plus(x('w$'), one), at('xm', 'b$', 'a$')))))} :
  {name: 'Inv2973: quorums overlap, or a config disabled', forall: 'a$', keys: ['b$', 'u$', 'w$'], holds: any(not(all(sz('a$'), sz('b$'))), disabled('a$'), disabled('b$'),
    not(all(less(at('xn', 'a$', 'b$'), plus(at('xm', 'a$', 'b$'), two(x('u$')))), less(at('xn', 'a$', 'b$'), plus(at('xm', 'b$', 'a$'), two(x('w$')))))),
    less(at('xn', 'a$', 'b$'), plus(x('u$'), x('w$'))))},
  inv === 'star'
    ? law('Inv*: no quorum of a config can still be gathered for a config term held', 'a$', ['j$'], [sz('a$'), sz('j$')], atMost(two(at('bq', 'a$', 'j$')), at('cfgSize', 'a$')))
    : {name: 'Inv3246: every quorum of a config has a term at least a config term held, or disabled', forall: 'a$', keys: ['j$'], holds: any(not(all(sz('a$'), sz('j$'))), disabled('a$'), atMost(two(at('low', 'a$', 'j$')), at('cfgSize', 'a$')))},
  law('p1: an uncopied server has no config', 'a$', ['c$'], [is('CV', 'a$', 0), sz('a$'), sz('c$')], same(get('Config', plus(times(N, x('a$')), x('c$'))), zero)),
  law('p2: before start no terms and no primary', 'a$', [], [unstarted, sz('a$')], [is('CfgT', 'a$', 0), is('St', 'a$', 0), is('CT', 'a$', 0)]),
]
return {m,laws:[...r.kindLaws(),...laws],r}
}

if(import.meta.main){
const [port = 'pstar', inv = 'star', msArg = '600000'] = process.argv.slice(2)
if (port !== 'pstar') throw new Error('This worktree implements P*: use pstar, not the archived cur port')
const {m,laws}=mldrHandSet(inv,process.env.LAB_OVERLAP_FORM==='uw'?'uw':'half')
let dumped = 0
const dumpDir = process.env.DUMP_DIR
if (dumpDir) {
  mkdirSync(dumpDir, {recursive: true})
  writeFileSync(`${dumpDir}/input.json`, JSON.stringify({m, laws}))
  countsDump.on = (g: any) => {
    const name = `${dumped++}.json`
    writeFileSync(`${dumpDir}/${name}`, JSON.stringify({...g, kind: 'grow', goal: {name: g.goal, hyps: g.hyps}}))
    console.error(`dump ${name}`)
  }
}
const ms = Number(msArg), t = performance.now()
console.error(`probe ${port} ${inv}: ${laws.length} laws, counts ${Object.keys(m.counts??{}).join(' ')}, ms ${ms}, GDP_COUNTS_GIVEN=${process.env.GDP_COUNTS_GIVEN}`)
const out = searchCounted(m, laws, ms)
console.log(JSON.stringify({port, inv, ms: Math.round(performance.now() - t), proven: out.proven, why: out.why, laws: out.laws.map(l => l.name)}))
}
