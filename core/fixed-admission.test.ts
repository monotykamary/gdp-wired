import {expect, test} from 'bun:test'
import {verdictOf} from './dsl.ts'

test('public DSL never labels an unchecked candidate PROVEN', () => {
  const candidate = {proven: true, checked: false, nodes: 1, leaves: 1}
  expect(verdictOf(candidate)).toMatchObject({proven: false, checked: false, stuck: 'unknown', why: 'kernel rejected the candidate proof'})
  expect(verdictOf({...candidate, checked: true})).toMatchObject({proven: true, checked: true})
})
