import {expect, test} from 'bun:test'
import {readFileSync} from 'node:fs'
import {type RecallSide, scoreRecall} from './score.ts'
const side = (version: string, verdict: string): RecallSide => ({version, status: 'checked', result: {rules: [{ok: true, entry: 'Handler', laws: [{name: 'policy', expr: 'result implies admin', verdict, run: ['run'], replayed: 'original code agrees'}]}]}})
test('recall requires the same stated policy, original replay and fixed counterpart', () => {
  const a = side('vulnerable', 'broken'), b = side('fixed', 'proven')
  expect(scoreRecall([a,b]).found).toBe(true)
  expect(scoreRecall([a,side('fixed','unknown')]).found).toBe(true)
  expect(scoreRecall([a,side('fixed','broken')]).found).toBe(false)
  expect(scoreRecall([a]).found).toBe(false)
  b.result!.rules[0]!.laws[0]!.expr = 'another policy'
  expect(scoreRecall([a,b]).found).toBe(false)
})
test('deliberate training flaws require reproduction but no fictional fixed revision', () => {
  const a = side('vulnerable', 'broken')
  expect(scoreRecall([a], true).found).toBe(true)
  expect(scoreRecall([a]).found).toBe(false)
  a.result!.rules[0]!.ok = false
  expect(scoreRecall([a], true).found).toBe(false)
})

test('refusals, absent laws and un-replayed environment schedules never count', () => {
  const a = side('vulnerable', 'broken'), b = side('fixed', 'proven')
  a.result!.rules[0]!.ok = false
  expect(scoreRecall([a,b]).found).toBe(false)
  a.result!.rules[0]!.ok = true
  delete a.result!.rules[0]!.laws[0]!.replayed
  expect(scoreRecall([a,b]).found).toBe(false)
  a.result!.rules[0]!.laws = []
  expect(scoreRecall([a,b]).found).toBe(false)
  const runtime = {version: 'vulnerable', status: 'runtime-only', accepted: true}
  expect(scoreRecall([runtime], true).found).toBe(false)
  expect(scoreRecall([runtime, {version: 'fixed', status: 'runtime-only'}]).found).toBe(false)
})

type Seed = {id: string, set: string, advisory: string, repo: string, before: string, after?: string, path: string, entry: string, policy: string, fixEvidence?: string, cve?: string | null}
const seeds = JSON.parse(readFileSync(new URL('./cases.json', import.meta.url), 'utf8')) as Seed[]
test('published recall seeds are distinct pinned policy cases with explicit fixes', () => {
  const published = seeds.filter(c => c.set === 'published')
  expect(published.length).toBeGreaterThanOrEqual(15)
  expect(new Set(seeds.map(c => c.id)).size).toBe(seeds.length)
  expect(new Set(published.map(c => c.advisory)).size).toBe(published.length)
  const cves = published.flatMap(c => c.cve ? [c.cve] : [])
  expect(new Set(cves).size).toBe(cves.length)
  for (const c of seeds) {
    expect(c.id).toMatch(/^[a-z0-9-]+$/)
    expect(c.repo).toMatch(/^[\w-]+\/[\w.-]+$/)
    expect(c.before).toMatch(/^[a-f0-9]{40}$/)
    expect(c.path.startsWith('/')).toBe(false)
    expect(c.path.split('/')).not.toContain('..')
    expect(c.entry).toBeTruthy()
    expect(c.policy).toBeTruthy()
    if (c.set === 'published') {
      expect(c.advisory).toMatch(/^https:\/\/github\.com\/advisories\/GHSA-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}$/)
      expect(c.after).toMatch(/^[a-f0-9]{40}$/)
      expect(c.before).not.toBe(c.after)
      expect(c.fixEvidence).toBe(`https://github.com/${c.repo}/commit/${c.after}`)
    } else expect(c.set).toBe('training')
  }
})

test('published measurement covers both exact revisions without hiding refusals', () => {
  type Row = {id: string, set: string, found: boolean, sides: {version: string, sha: string, sourceSha256: string, status: string}[]}
  const m = JSON.parse(readFileSync(new URL('./measurement.json', import.meta.url), 'utf8')) as {rows: Row[], published: {found: number, total: number}, training: {found: number, total: number}}
  expect(m.rows.map(r => r.id)).toEqual(seeds.map(c => c.id))
  for (const c of seeds) {
    const r = m.rows.find(r => r.id === c.id)!
    expect(r.set).toBe(c.set)
    expect(r.sides.map(s => s.version)).toEqual(c.after ? ['vulnerable', 'fixed'] : ['vulnerable'])
    for (const s of r.sides) {
      expect(s.sha).toBe(s.version === 'vulnerable' ? c.before : c.after ?? '')
      expect(s.sourceSha256).toMatch(/^[a-f0-9]{64}$/)
      expect(s.status).not.toBe('error')
    }
  }
  for (const set of ['published', 'training'] as const) {
    const rows = m.rows.filter(r => r.set === set)
    expect(m[set]).toEqual({found: rows.filter(r => r.found).length, total: rows.length})
  }
})
