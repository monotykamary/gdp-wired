import {expect, test} from 'bun:test'
import {orderCountOperations, type CountOperationKind} from './count-operation-order.ts'
test('counted cases try costly uncertain shapes first without mutating inputs', () => {
  const cases: {value: number, kind: CountOperationKind}[] = [{value: 17, kind: 'phase'}, {value: 4, kind: 'replacement'}, {value: 92, kind: 'leader'}, {value: 0, kind: 'copy'}, {value: 16, kind: 'phase'}]
  const before = JSON.stringify(cases)
  expect(orderCountOperations(cases).map(c => c.value)).toEqual([92, 0, 4, 16, 17])
  expect(orderCountOperations(cases, 'original').map(c => c.value)).toEqual([0, 4, 16, 17, 92])
  expect(JSON.stringify(cases)).toBe(before)
})
