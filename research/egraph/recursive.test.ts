import {expect, test} from 'bun:test'
import {prepareLemma, recursiveExperiment} from './recursive.ts'
import {refuseCyclic} from '../../kernel/cyclic.ts'

test('a proved reverse/append lemma is matched at a recursive tail, used, and indispensable', () => {
  const prepared = prepareLemma(), v = prepared.verdict
  expect(v.proven && v.checked && v.proof?.proven).toBe(true)
  if (!v.proof?.proven || v.node === undefined) throw new Error(JSON.stringify({goal: v.goal, stuck: v.stuck, node: v.node}))
  const lemma = v.proof.proof, root = v.node
  expect(refuseCyclic(lemma)).toBeUndefined()
  const baseline = recursiveExperiment(lemma, root, false)
  const enabled = recursiveExperiment(lemma, root, true)
  expect(baseline.checked).toBe(false)
  expect(enabled.checked).toBe(true)
  expect(enabled.matches).toBeGreaterThan(0)
  expect(enabled.lemmaUses).toBeGreaterThan(0)
  expect(enabled.removedUse).toBeDefined()
  expect(enabled.badRank).toBeDefined()
  const bad = structuredClone(lemma)
  bad.nodes[root]!.main = {leaf: []}
  expect(() => recursiveExperiment(bad, root, true)).toThrow('unchecked lemma')
}, 60000)
