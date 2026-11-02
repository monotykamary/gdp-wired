// probe (gen/laneY6): mldr with Endive's inductive invariant written over counts (one parameter: a config's size and
// its members not newer than its owner; two, Lane C3's: |X \ Y|, |X ∩ Y| over a pair of servers and a config's members
// below a server's config term), proven by core/counts.ts's searchCounted with the laws as callers.
import {protocols} from './models.ts'
import {type C, type E, type Law, type Machine, all, any, atMost, get, ite, less, n, not, plus, same, times, x} from '../../../core/machine.ts'
import {countsDump, searchCounted} from '../../../core/counts.ts'
const N = 64
const p = protocols.find(q => q.id === 'mldr')!, r: any = p.make(), m0: Machine = r.machine
const one = n(1), zero = n(0), ind = (c: C): E => ite(c, one, zero)
const cfg = (s: E, k: E) => same(get('Config', plus(times(N, s), k)), one)
const newer = (a: E, b: E): C => any(less(get('CfgT', b), get('CfgT', a)), all(same(get('CfgT', a), get('CfgT', b)), less(get('CV', b), get('CV', a))))
const counts: Machine['counts'] = {
  ...m0.counts,
  cfgSize: {j: 'cj', key: 'ck', below: x('size'), body: ind(cfg(x('cj'), x('ck')))},
  old: {j: 'oj', key: 'ok', below: x('size'), body: ind(all(cfg(x('oj'), x('ok')), not(newer(x('ok'), x('oj')))))},
  xm: {j: 'mj', lo: 'ml', base: N, key: 'mk', below: x('size'), body: ind(all(cfg(x('mj'), x('mk')), not(cfg(x('ml'), x('mk')))))},
  xn: {j: 'nj', lo: 'nl', base: N, key: 'nk', below: x('size'), body: ind(all(cfg(x('nj'), x('nk')), cfg(x('nl'), x('nk'))))},
  low: {j: 'lj', lo: 'll', base: N, key: 'lk', below: x('size'), body: ind(all(cfg(x('lj'), x('lk')), less(get('CT', x('lk')), get('CfgT', x('ll')))))},
}
const m: Machine = {...m0, counts}
const started = same(x('started'), one), sz = (v: string) => less(x(v), x('size'))
const pair = (c: string, a: string, b: string): E => get(c, plus(times(N, x(a)), x(b)))
const disabled = (i: string): C => atMost(times(2, get('old', x(i))), get('cfgSize', x(i)))
const laws: Law[] = [
  ...p.laws(r),
  {name: 'a copied config is the one picked', forall: 'a$', keys: ['c$'], holds: any(not(all(same(x('started'), zero), same(get('Copied', x('a$')), one), sz('a$'), sz('c$'))), same(get('Config', plus(times(N, x('a$')), x('c$'))), get('C0', x('c$'))))},
  {name: 'before start, version 1', forall: 'a$', holds: any(not(all(same(x('started'), zero), sz('a$'))), same(get('CV', x('a$')), one))},
  {name: 'a primary at its config term', forall: 'a$', holds: any(not(all(started, sz('a$'), same(get('St', x('a$')), one))), same(get('CfgT', x('a$')), get('CT', x('a$'))))},
  {name: 'one config term, one primary newest', forall: 'a$', keys: ['b$'], holds: any(not(all(started, sz('a$'), sz('b$'), same(get('CfgT', x('a$')), get('CfgT', x('b$'))), same(get('St', x('a$')), one))), not(newer(x('b$'), x('a$'))))},
  {name: 'one version and term, one config', forall: 'a$', keys: ['b$', 'c$'], holds: any(not(all(started, sz('a$'), sz('b$'), sz('c$'), same(get('CV', x('a$')), get('CV', x('b$'))), same(get('CfgT', x('a$')), get('CfgT', x('b$'))))), same(get('Config', plus(times(N, x('a$')), x('c$'))), get('Config', plus(times(N, x('b$')), x('c$')))))},
  {name: 'quorums overlap, or a config disabled', forall: 'a$', keys: ['b$', 'u$', 'w$'], holds: any(not(all(started, sz('a$'), sz('b$'))), disabled('a$'), disabled('b$'),
    not(all(less(pair('xn', 'a$', 'b$'), plus(pair('xm', 'a$', 'b$'), times(2, x('u$')))), less(pair('xn', 'a$', 'b$'), plus(pair('xm', 'b$', 'a$'), times(2, x('w$')))))),
    less(pair('xn', 'a$', 'b$'), plus(x('u$'), x('w$'))))},
  {name: 'every quorum at a config term, or disabled', forall: 'a$', keys: ['b$'], holds: any(not(all(started, sz('a$'), sz('b$'))), disabled('b$'), atMost(times(2, pair('low', 'b$', 'a$')), get('cfgSize', x('b$'))))},
]
let dumps = 0
countsDump.on = (g: any) => { if (!/one primary per term/.test(g.law) || (g.ls?.length ?? 0) < 30 || dumps++ > 1) return; console.log('DUMP', g.law, '|', g.goal, '|', JSON.stringify(Object.fromEntries(Object.entries(g.witness ?? {}).filter(([k2, v2]) => (v2 as number) !== 0 && !k2.startsWith('Copied') && !k2.startsWith('w?')))).slice(0, 4000)) }
const ms = Number(process.argv[2] ?? 300_000), t = performance.now()
const out = searchCounted(m, [...r.kindLaws(), ...laws], ms)
console.log(JSON.stringify({ms: Math.round(performance.now() - t), proven: out.proven, why: out.why}).slice(0, 600))
