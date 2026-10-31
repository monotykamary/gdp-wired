// The one generator (machine.ts's lcg and seeded, data.ts's rng): x' = (1103515245 x + 12345) mod 2^31 as BigInt
// arithmetic computes it, step for step, and no cycle under 10^6 steps from any seed, the ones the float form folded
// into its shortest cycles among them (9: 61 steps, 7633: 247, 6961: 220, 8595: 378; the rest into 10,466).
import {expect, test} from 'bun:test'
import {lcg, seeded} from './machine.ts'
import {rng} from './data.ts'

const SEEDS = [0, 1, 7, 9, 42, 777, 4242, 6961, 7633, 8595, 12345, 2 ** 31 - 1]

test('every step is the BigInt reference', () => {
  for (const s of SEEDS) {
    let x = s, r = BigInt(s)
    const draw = seeded(s), unit = rng(s)
    for (let i = 0; i < 100_000; i++) {
      x = lcg(x)
      r = (r * 1103515245n + 12345n) % 2n ** 31n
      if (BigInt(x) !== r) throw new Error(`seed ${s}, step ${i}: ${x}, the reference ${r}`)
      const k = 1 + (i % 97)
      if (draw(k) !== Number((r * BigInt(k)) >> 31n)) throw new Error(`seed ${s}, step ${i}: seeded's draw of ${k}`)
      if (unit() !== Number(r) / 2 ** 31) throw new Error(`seed ${s}, step ${i}: rng's draw`)
    }
  }
})

test('no cycle under 10^6 steps', () => {
  for (const s of SEEDS) {
    const seen = new Set<number>()
    let x = lcg(s)
    for (let i = 0; i < 1_000_000; i++) {
      if (seen.has(x)) throw new Error(`seed ${s}: a cycle after ${i} steps`)
      seen.add(x)
      x = lcg(x)
    }
    expect(seen.size).toBe(1_000_000)
  }
}, 120_000)
