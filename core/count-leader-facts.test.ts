import {expect, test} from 'bun:test'
import {type GuardCountProposal} from './count-guard-facts.ts'
import {leaderCountProposals} from './count-leader-facts.ts'
const proposal = (kind: string, sign = 1): GuardCountProposal => ({name: 'arbitrary ' + kind + sign, kind, when: [], terms: [[sign, 'post'], [-sign, 'pre']]})
test('leader facts select structural complement upper and row lower proposals', () => {
  const upper = proposal('guard-complement-upper'), lower = proposal('row-frame', -1)
  const all = [proposal('guard-intersection-lower'), proposal('row-frame'), upper, lower, proposal('unrelated')], before = JSON.stringify(all)
  expect(leaderCountProposals(all)).toEqual([upper, lower])
  expect(JSON.stringify(all)).toBe(before)
})
test('leader fact selection remains bounded and preserves proposal order', () => {
  const all = Array.from({length: 25}, (_, i) => ({...proposal('guard-complement-upper'), name: String(i)}))
  expect(leaderCountProposals(all)).toEqual(all.slice(0, 24))
  expect(leaderCountProposals([])).toEqual([])
  expect(leaderCountProposals([{...proposal('row-frame', -1), terms: []}])).toEqual([])
})
