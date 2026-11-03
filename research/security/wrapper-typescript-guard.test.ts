import {expect, test} from 'bun:test'
import {assertConsumerTypeScript, type ConsumerTypeScript} from './wrapper-typescript-guard.ts'

const expected: ConsumerTypeScript = {path: '/owned/consumer/node_modules/typescript/lib/typescript.js', version: '5.9.3'}

test('exact consumer TypeScript path and version permit dispatch', () => {
  let dispatches = 0
  assertConsumerTypeScript({...expected}, expected)
  dispatches++
  expect(dispatches).toBe(1)
})

test('a different owned path rejects before dispatch even at the correct version', () => {
  for (const path of ['/owned/other/node_modules/typescript/lib/typescript.js', expected.path + '.other']) {
    let dispatches = 0
    expect(() => { assertConsumerTypeScript({...expected, path}, expected); dispatches++ }).toThrow('owned TypeScript path mismatch')
    expect(dispatches).toBe(0)
  }
})

test('a different installed version rejects before dispatch at the exact path', () => {
  for (const version of ['5.9.2', '5.10.0', '6.0.0']) {
    let dispatches = 0
    expect(() => { assertConsumerTypeScript({...expected, version}, expected); dispatches++ }).toThrow('owned TypeScript version mismatch')
    expect(dispatches).toBe(0)
  }
})

test('mismatched path and version cannot dispatch', () => {
  let dispatches = 0
  expect(() => { assertConsumerTypeScript({path: '/owned/other/typescript.js', version: '5.9.2'}, expected); dispatches++ }).toThrow('owned TypeScript path mismatch')
  expect(dispatches).toBe(0)
})
