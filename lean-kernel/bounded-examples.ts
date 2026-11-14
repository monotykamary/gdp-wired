// Actual new marked machines sent to the unchanged Sets/CountMachine checker.
// Run through scripts/bapa-export.sh on the supercomputer, never locally.
import {writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {type C, type Law, type Machine, n, x, same, less, get, plus, times} from '../core/machine.ts'
import {toLean} from './emit.ts'
import {boundedRegions} from './bounded-regions.ts'
const q = (body: C): C => ({op: 'all', key: 'k', finite: 'Item', c: {op: 'or', xs: [{op: 'not', x: less(x('k'), x('size'))}, body]}})
const base = (body: C): Machine => ({name: 'finite-guarded', params: ['size'], inputs: [], state: {s: n(1)}, step: {flags: {p: q(body)}, state: {s: {op: 'if', c: {op: 'flag', name: 'p'}, then: n(1), else: n(0)}}}})
const law: Law = {name: 'guard holds', holds: same(x('s'), n(1))}
const arithmetic = base(same(times(2, x('k')), plus(x('k'), x('k'))))
const functions = {...base(same(get('F', times(2, x('k'))), get('F', plus(x('k'), x('k'))))), fns: {F: {js: 'k => k * k', lean: '(fun k : Nat => k * k)'}}}
const empty = {...base(same(n(0), n(1))), pre: same(x('size'), n(0))}
const items = [{id: 'finite_arithmetic', machine: arithmetic, laws: [law]}, {id: 'finite_function', machine: functions, laws: [law]}, {id: 'finite_empty', machine: empty, laws: [law]}]
const out = process.env.SUPERCOMPUTER_OUTPUT_DIR!
writeFileSync(join(out, 'BoundedExamples.lean'), toLean([...items, ...boundedRegions()], {native: false, cyclic: false}))
writeFileSync(join(out, 'machines.json'), JSON.stringify(items, null, 2) + '\n')
