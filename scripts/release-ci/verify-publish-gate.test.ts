import {describe, expect, test} from 'bun:test'
import {validateReleaseGateStatus} from './verify-publish-gate'

const commit = 'a'.repeat(40)
const digest = 'b'.repeat(64)
const status = () => ({sha: commit, total_count: 1, statuses: [{context: 'release-full-gate', state: 'success', description: `receipt-sha256:${digest}`}]})
const check = (body: unknown, httpStatus = 200) => validateReleaseGateStatus(httpStatus, body, commit, digest)

describe('external release gate commit status', () => {
  test('accepts the exact commit and receipt digest', () => expect(() => check(status())).not.toThrow())
  test('rejects missing status', () => expect(() => check({...status(), total_count: 0, statuses: []})).toThrow())
  test.each(['failure', 'error', 'pending'])( 'rejects %s', state => {
    const body = status(); body.statuses[0]!.state = state
    expect(() => check(body)).toThrow()
  })
  test('rejects a different response sha', () => expect(() => check({...status(), sha: 'c'.repeat(40)})).toThrow())
  test('rejects a different receipt digest', () => {
    const body = status(); body.statuses[0]!.description = `receipt-sha256:${'c'.repeat(64)}`
    expect(() => check(body)).toThrow()
  })
  test('rejects ambiguous duplicate contexts', () => {
    const body = status(); body.statuses.push({...body.statuses[0]!}); body.total_count = 2
    expect(() => check(body)).toThrow()
  })
  test('rejects an incomplete status response', () => expect(() => check({...status(), total_count: 2})).toThrow())
  test.each([401, 403, 404, 500])('rejects HTTP %i even with a success body', code => expect(() => check(status(), code)).toThrow())
})
