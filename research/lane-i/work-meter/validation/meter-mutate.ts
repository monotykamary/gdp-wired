import {strict as assert} from 'node:assert'
import {afterAll} from 'bun:test'
import {kernelMeter} from '../../../kernel/meter.ts'

const mode = process.env.METER_MUTATION ?? 'plain'
assert(['plain', 'zero', 'double', 'random'].includes(mode))
let writes = 0, seed = 0x1731a
if (mode !== 'plain') for (const key of ['tableCells', 'checkSteps', 'astNodes', 'evals', 'cubeTests', 'ticks'] as const) {
  let stored = 0
  Object.defineProperty(kernelMeter, key, {
    enumerable: true, configurable: true,
    get: () => stored,
    set: (value: number) => {
      writes++
      if (mode === 'zero') stored = 0
      else if (mode === 'double') stored += 2 * (value - stored)
      else { seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; stored = seed }
    },
  })
}
console.log('KERNEL_METER_PRELOAD ' + JSON.stringify({mode, installed: true}))
afterAll(() => {
  const exercised = mode === 'plain' ? kernelMeter.tableCells > 0 && kernelMeter.checkSteps > 0 : writes > 0
  console.log('KERNEL_METER_MUTATION ' + JSON.stringify({mode, writes, exercised, values: kernelMeter}))
})
