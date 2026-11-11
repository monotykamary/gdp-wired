import {expect, test} from 'bun:test'
import {atMost, n} from '../machine.ts'
import {type Path, type Tree, canon, check} from '../../kernel/kernel.ts'
import {clock, rowsAt} from '../../kernel/prove.ts'
import {reframeCountTree} from './reframe-tree.ts'
const goal = {name: 'contradiction', hyps: [atMost(n(1), n(0))]}, split = {branch: 1}, extra = {extra: 1}
const child = (holds: boolean): Path => new Map([[canon(split), {lin: split, holds}]])
const leaf = (path: Path): Tree => ({leaf: [{kind: 'input', index: rowsAt(goal, path).findIndex(row => row.lin['1'] === 1 && Object.keys(row.lin).length === 1)}]})
const frame = (path: Path): Path => path.get(canon(split))?.holds ? new Map([[canon(extra), {lin: extra, holds: true}], ...path]) : path

test('reindex every leaf when a conditional frame activates below the root', () => {
  const yes = child(true), no = child(false), original: Tree = {split, yes: leaf(yes), no: leaf(no)}
  expect(check(goal, original)).toBe(true)
  expect(check(goal, original.yes, frame(yes))).toBe(false)
  const tree = reframeCountTree(goal, original, new Map(), new Map(), frame, clock() + 1000)
  expect(tree && !('leaf' in tree)).toBe(true)
  if (!tree || 'leaf' in tree) return
  expect(check(goal, tree.yes, frame(yes))).toBe(true)
  expect(check(goal, tree.no, frame(no))).toBe(true)
})
test('missing source assumptions and corrupted leaf proofs are refused', () => {
  const possible = {name: 'possible', hyps: []}, from: Path = new Map([['impossible', {lin: {'1': 1}, holds: true}]])
  expect(reframeCountTree(possible, {leaf: [{kind: 'input', index: 0}]}, from, new Map(), p => p, clock() + 1000)).toBeUndefined()
  expect(reframeCountTree(goal, {leaf: []}, new Map(), new Map(), frame, clock() + 1000)).toBeUndefined()
})
test('expired or repeated-split transports do not produce a certificate', () => {
  expect(reframeCountTree(goal, leaf(new Map()), new Map(), new Map(), frame, clock() - 1)).toBeUndefined()
  const tree: Tree = {split, yes: leaf(child(true)), no: leaf(child(false))}
  expect(reframeCountTree(goal, tree, child(true), child(true), frame, clock() + 1000)).toBeUndefined()
})
