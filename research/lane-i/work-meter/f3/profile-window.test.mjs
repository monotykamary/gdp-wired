import {test} from 'node:test'
import {strict as assert} from 'node:assert'
import {selectProfileWindow} from './profile-window.mjs'
const frame = name => ({functionName: name, scriptId: '1', url: 'file:///fixture.mjs', lineNumber: 1, columnNumber: 0})
const profile = (samples, timeDeltas, endTime = 1000000) => ({startTime: 0, endTime, samples, timeDeltas, nodes: [
  {id: 1, callFrame: frame('(root)'), children: [2, 3]}, {id: 2, callFrame: frame('stale')}, {id: 3, callFrame: frame('recent')},
]})
test('timestamp filtering excludes a dominant old sample-count suffix', () => {
  const p = profile([...Array(25).fill(2), 3, 3], [...Array(25).fill(1000), 775000, 100000])
  const result = selectProfileWindow(p, 250)
  assert.equal(result.timing.valid, true)
  assert.equal(result.timing.samplesInWindow, 2)
  assert.deepEqual(result.stack.map(item => item.functionName), ['recent', '(root)'])
  assert.equal(result.timing.firstSampleUs, 800000)
  assert.equal(result.timing.latestSampleAgeMs, 100)
  assert.equal(result.timing.maxSampleGapMs, 100)
})
test('a quiet window without CPU samples stays unattributed', () => {
  const result = selectProfileWindow(profile(Array(25).fill(2), Array(25).fill(1000)), 250)
  assert.equal(result.timing.valid, true); assert.equal(result.timing.samplesInWindow, 0)
  assert.deepEqual(result.stack, []); assert.equal(result.timing.latestSampleAgeMs, null)
  assert.equal(result.timing.maxSampleGapMs, 250)
})
test('both time-window boundaries are inclusive and ties prefer the latest sample', () => {
  const p = profile([2, 3], [750000, 250000])
  assert.equal(selectProfileWindow(p, 250).timing.samplesInWindow, 2)
  assert.equal(selectProfileWindow(p, 250).stack[0].functionName, 'recent')
  assert.equal(selectProfileWindow(p, 0).timing.samplesInWindow, 1)
})
test('a short profile never reads before its start', () => {
  const result = selectProfileWindow(profile([3], [5000], 10000), 250)
  assert.equal(result.timing.lowerBoundUs, 0); assert.equal(result.timing.maxSampleGapMs, 5)
})
test('empty timestamped profiles are valid and unattributed', () => {
  const result = selectProfileWindow(profile([], []), 250)
  assert.equal(result.timing.valid, true); assert.deepEqual(result.stack, [])
})
test('missing or mismatched timestamps fail closed', () => {
  for (const p of [profile([2], []), {...profile([2], [1]), timeDeltas: undefined}]) {
    const result = selectProfileWindow(p, 250)
    assert.equal(result.timing.valid, false); assert.deepEqual(result.stack, [])
  }
})
test('invalid timing values fail closed', () => {
  for (const p of [profile([2], [-1]), profile([2], [Infinity]), profile([2], [1000001]), {...profile([], []), startTime: NaN}]) assert.equal(selectProfileWindow(p, 250).timing.valid, false)
  assert.equal(selectProfileWindow(profile([], []), -1).timing.valid, false)
})
test('invalid delta diagnostics preserve the exact sample and fail closed', () => {
  for (const delta of [-7, NaN, Infinity]) {
    const result = selectProfileWindow(profile([2, 3], [750000, delta]), 250)
    assert.equal(result.timing.valid, false)
    assert.equal(result.timing.reason, 'invalid sample delta')
    assert.equal(result.timing.invalidSampleIndex, 1)
    assert.equal(result.timing.invalidSampleDeltaUs, Number.isFinite(delta) ? delta : String(delta))
    assert.equal(result.timing.previousSampleUs, 750000)
    assert.equal(result.timing.profileEndUs, 1000000)
    assert.deepEqual(result.stack, [])
  }
})
test('unknown nodes and cyclic stacks fail closed', () => {
  assert.equal(selectProfileWindow(profile([99], [1000000]), 250).timing.valid, false)
  const p = profile([2], [1000000])
  p.nodes[0].children = []; p.nodes[1].children = [3]; p.nodes[2].children = [2]
  assert.equal(selectProfileWindow(p, 250).timing.valid, false)
})
