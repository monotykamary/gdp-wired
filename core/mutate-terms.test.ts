import {expect, test} from 'bun:test'
import {mkdtempSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {bool, fun, oneOf, upTo} from './dsl.ts'
import {checkMutations, deriveDecisionMutants} from './mutate.ts'
import type {Machine} from './machine.ts'

const machine = fun('synthetic admission').inputs({ready: bool, reviewed: bool, zone: oneOf('home', 'peer', 'other'), load: upTo(2)})
  .returns(({ready, reviewed, zone, load}) => ({ok: ready.and(reviewed, zone.is('home'), load.lt(2))})).rule.machine
const render = (m: Machine) => `export default ${JSON.stringify(m)}\n`
const options = {file: 'decision.ts', render, choices: {zone: [0, 1, 2]}}

test('term mutants are deterministic, bounded, isolated, and leave constraints untouched', () => {
  const before = JSON.stringify(machine), edits = deriveDecisionMutants(machine, options)
  expect(edits).toEqual(deriveDecisionMutants(machine, options))
  expect(JSON.stringify(machine)).toBe(before)
  expect(new Set(edits.map(e => e.to)).size).toBe(edits.length)
  for (const kind of ['negate-guard', 'drop-conjunct', 'widen-choice', 'flip-comparison']) expect(edits.some(e => e.name?.startsWith(kind))).toBe(true)
  for (const edit of edits) {
    const variant = JSON.parse(edit.to.slice('export default '.length)) as Machine
    expect(variant.assume).toEqual(machine.assume)
    expect(variant.pre).toEqual(machine.pre)
    expect(variant.state).toEqual(machine.state)
    expect(edit.from).toBe(render(machine))
  }
  expect(deriveDecisionMutants(machine, {...options, maxCandidates: 2})).toHaveLength(2)
  expect(deriveDecisionMutants(machine, {...options, render: () => 'same'})).toEqual([])
})

test('term mutants reject unsupported state and malformed domains/printers', () => {
  expect(() => deriveDecisionMutants({...machine, step: {state: {out: {op: 'var', name: 'out'}}}}, options)).toThrow('non-input state')
  expect(() => deriveDecisionMutants({...machine, maps: {M: 0}}, options)).toThrow('pure scalar')
  expect(() => deriveDecisionMutants(machine, {...options, choices: {missing: [0, 1]}})).toThrow('choice encodings')
  expect(() => deriveDecisionMutants(machine, {...options, choices: {zone: [0, 0]}})).toThrow('choice encodings')
  expect(() => deriveDecisionMutants(machine, {...options, render: () => ''})).toThrow('nonempty source')
  expect(() => deriveDecisionMutants(machine, {...options, maxCandidates: 0})).toThrow('maxCandidates')
})

test('derived candidates run through source mutation checks and attribute individual law kills', () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-term-mutants-'))
  const original = render(machine)
  writeFileSync(join(dir, 'decision.ts'), original)
  const interpreter = new URL('./machine.ts', import.meta.url).href
  const command = (law: string) => [process.execPath, '--eval', `
import machine from './decision.ts';
import {interpret} from ${JSON.stringify(interpreter)};
const r = interpret(machine), ps = {};
const failures = new Set();
for(let ready=0;ready<2;ready++)for(let reviewed=0;reviewed<2;reviewed++)for(let zone=0;zone<3;zone++)for(let load=0;load<3;load++){
  const out=r.step(ps,r.init(ps),{ready,reviewed,zone,load}).scalars['out.ok'];
  if(out&&!ready)failures.add('ready');
  if(out&&!reviewed)failures.add('reviewed');
  if(out&&zone!==0)failures.add('zone');
  if(out&&load>=2)failures.add('load');
  if(ready&&reviewed&&zone===0&&load<2&&!out)failures.add('admit-valid');
}
const killed=${JSON.stringify(law)}==='all-laws'?failures.size>0:failures.has(${JSON.stringify(law)});
if(killed)console.error([...failures].join(','));
process.exit(killed?1:0);
`]
  try {
    const names = ['all-laws', 'ready', 'reviewed', 'zone', 'load', 'admit-valid']
    const result = checkMutations({cwd: dir, mutants: deriveDecisionMutants(machine, options), lawSuite: 'all-laws', suites: names.map(name => ({name, command: command(name)}))})
    console.log(result.markdown)
    expect(result.rows.length).toBeGreaterThan(0)
    expect(result.passed).toBe(true)
    for (const row of result.rows) expect(names.slice(1).some(n => row.suites[n]!.status === 'caught')).toBe(true)
    expect(readFileSync(join(dir, 'decision.ts'), 'utf8')).toBe(original)
  } finally { rmSync(dir, {recursive: true, force: true}) }
}, 90000)
