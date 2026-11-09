import {expect, test} from 'bun:test'
import {parseMldrPair, parseTestSummary, parseReplayNegative} from './validation-audit.ts'
const side = (name: string, verdict = 'unknown') => [
  `LANE_I_BEGIN mldr 1 mldr ${name}`,
  `LANE_I_EXIT ${name} 0`,
  JSON.stringify({id: 'mldr', search: {verdict, ms: 59000}}),
  'LANE_I_TIMING {"event":"candidates","at":5000}',
  'counts: candidates at 0 ms: helper; one primary per term',
  'LANE_I_TIMING {"event":"first-attempt-return","at":10000,"attemptWallMs":1000}',
  'counts: try helper | ls 2 pass 1 ms 3000 took 120 wall 1000 [] -> kept',
  'LANE_I_TIMING {"event":"result","at":60000,"searchMs":59000}',
  `LANE_I_END mldr 1 mldr ${name}`,
].join('\n')
test('exit zero without a semantic result is not a successful receipt', () => {
  const log = side('base') + '\n' + side('candidate').split('\n').filter(line => !line.startsWith('{')).join('\n')
  expect(parseMldrPair(log, 1).issues).toContain('candidate: expected one semantic result')
})
test('unknown stays unknown and wall excludes the measured first attempt', () => {
  const got = parseMldrPair(side('base') + '\n' + side('candidate'), 1)
  expect(got.issues).toEqual([])
  expect(got.sides[1]!.result?.search.verdict).toBe('unknown')
  expect(got.sides[1]!.preAttemptWallMs).toBe(8000)
  expect(got.sides[1]!.generationWallMs).toBe(4000)
  expect(got.sides[1]!.kept?.[0]?.units).toBe(120)
})
test('duplicate or swapped phases and malformed results fail closed', () => {
  expect(parseMldrPair(side('base') + '\n' + side('candidate') + '\n' + side('candidate'), 1).issues).toContain('candidate: phase cardinality/order')
  expect(parseMldrPair(side('base') + '\n' + side('candidate', 'green'), 1).issues).toContain('candidate: invalid strict result')
  expect(parseMldrPair(side('base') + '\n' + side('candidate').replace('"ms":59000', '"ms":61000'), 1).issues).toContain('candidate: invalid strict result')
})
test('a replay control requires the specific metadata rejection, not just an exit marker', () => {
  const log = '(fail) ordinary core replay retains metadata\n0 pass\n1 fail\n"readsRetained": false\n"certificatesRetained": true\n"poolsRetained": true\nCORE_REPLAY_NEGATIVE_CONTROL_OK'
  expect(parseReplayNegative(log)).toEqual({issues: [], expectedRejection: true})
  for (const bad of [log.replace('false', 'true'), log.replace('1 fail', '0 fail'), log + '\n1 error', log + '\nCORE_REPLAY_NEGATIVE_CONTROL_OK', 'CORE_REPLAY_NEGATIVE_CONTROL_OK']) expect(parseReplayNegative(bad).issues.length).toBe(1)
})
test('a passing test beside a load error is not a clean test summary', () => {
  expect(parseTestSummary('1 pass\n0 fail\n1 error\n1 expect() calls').issues.length).toBe(1)
  expect(parseTestSummary('1 pass\n0 fail\n4 expect() calls')).toEqual({issues: [], passed: 1, assertions: 4})
  expect(parseTestSummary('1 pass\n0 fail\n1 pass\n0 fail').issues.length).toBe(1)
})
