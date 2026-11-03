import {expect, test} from 'bun:test'
import {mkdtempSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {asBroken, compareTasks, differing, VIEWS, type Obs} from './bar-lib'

const obs = (answer: string, extra: Partial<Obs> = {}): Obs => ({answer, solved: true, secs: 1, ...extra})
const cmp = (cand: Obs[], base: Obs[]) => compareTasks(['task'], new Map([['task', {cand, base}]]), 60)[0]!

test('successful refusals with different diagnostics are not contradictory decisions', () => {
  const cand = obs('broken: timeout', {decision: 'refused'})
  const base = obs('broken: refused', {decision: 'refused'})
  expect(differing(new Map([['task', cand]]), [new Map([['task', base]])])).toEqual([])
  const r = cmp([cand, base], [base, base])
  expect(r.kind).toBe('noise')
  expect(r.samples.cand[0]!.answer).toBe('broken: timeout')
})

test('opposite decided answers and explicit wrong verdicts are still wrong', () => {
  for (const [a, b] of [['sat', 'unsat'], ['terminates', 'nonterminating']]) {
    expect(cmp([obs(a!)], [obs(b!)]).kind).toBe('wrong')
    expect(differing(new Map([['task', obs(a!)]]), [new Map([['task', obs(b!)]])])).toEqual(['task'])
  }
  expect(cmp([obs('broken: proven', {wrong: true, solved: false})], [obs('broken: refused', {decision: 'refused'})]).kind).toBe('wrong')
  expect(cmp([obs('same', {wrong: true, decision: 'same'})], [obs('same')]).kind).toBe('wrong')
})

test('broken normalization is idempotent and preserves a wrong proof for calibration', () => {
  const wrong = asBroken(obs('proven'))
  expect(wrong).toMatchObject({answer: 'broken: proven', solved: false, wrong: true})
  expect(asBroken(wrong)).toBe(wrong)
  expect(cmp([asBroken(wrong)], [asBroken(obs('timeout', {solved: false}))]).kind).toBe('wrong')
  const refused = asBroken(obs('timeout', {solved: false}))
  expect(asBroken(refused)).toBe(refused)
  expect(refused).toMatchObject({answer: 'broken: timeout', decision: 'refused', solved: true, wrong: false})
})

test('ordinary solid gains and losses retain their meaning', () => {
  const won = obs('proven'), no = obs('unknown', {solved: false})
  expect(cmp([won, won, won], [no, no, no])).toMatchObject({kind: 'gained', solid: true})
  expect(cmp([no, no, no], [won, won, won])).toMatchObject({kind: 'lost', solid: true})
})

test('frontier reader preserves timeout details while identifying refusal and detecting a broken proof', () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-bar-'))
  try {
    writeFileSync(join(dir, 'broken.json'), JSON.stringify(['timeout', 'refused', 'false proof']))
    for (const [id, result] of Object.entries({
      timeout: {proven: false, checked: false, timeout: true, ms: 60000},
      refused: {proven: false, checked: false, ms: 1000},
      'false proof': {proven: true, checked: true, ms: 1000},
      'ordinary timeout': {proven: false, checked: false, timeout: true, ms: 60000},
    })) writeFileSync(join(dir, `${id}.log`), `${id}\n${JSON.stringify(result)}\n`)
    const rows = VIEWS.f2!.parse(dir, '')
    expect(rows.get('timeout')).toMatchObject({answer: 'broken: timeout', decision: 'refused', solved: true, wrong: false})
    expect(rows.get('refused')).toMatchObject({answer: 'broken: refused', decision: 'refused', solved: true, wrong: false})
    expect(rows.get('false proof')).toMatchObject({answer: 'broken: proven', solved: false, wrong: true})
    expect(rows.get('ordinary timeout')).toMatchObject({answer: 'timeout', solved: false, wrong: false})
    expect(cmp([rows.get('timeout')!], [rows.get('refused')!]).kind).toBe('noise')
    expect(cmp([rows.get('false proof')!], [rows.get('refused')!]).kind).toBe('wrong')
  } finally { rmSync(dir, {recursive: true, force: true}) }
})
