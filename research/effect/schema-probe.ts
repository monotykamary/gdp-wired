// Temporary Boat-only inspection of the pinned Effect ASTs. Never used by the adapter.
import * as E4 from 'effect'
import * as E3 from 'effect3'
import {readFileSync} from 'node:fs'
// eslint-disable-next-line @typescript-eslint/no-explicit-any
const summarize = (x: any, depth = 0): unknown => {
  if (typeof x === 'function') return '<function>'
  if (typeof x === 'symbol') return String(x)
  if (x === null || typeof x !== 'object') return x
  if (depth > 9) return '<depth>'
  if (Array.isArray(x)) return x.map(v => summarize(v, depth + 1))
  return Object.fromEntries(Reflect.ownKeys(x).map(k => [String(k), summarize(x[k], depth + 1)]))
}
for (const [E, version] of [[E3, 3], [E4, 4]] as const) {
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const S: any = E.Schema
  const filters = version === 4 ? {
    bounds: S.Int.check(S.isGreaterThan(-3), S.isLessThanOrEqualTo(7)),
    between: S.Int.check(S.isBetween({minimum: -3, maximum: 7})),
    custom: S.Int.check(S.makeFilter((x: number) => x !== 3)),
  } : {
    bounds: S.Int.pipe(S.greaterThan(-3), S.lessThanOrEqualTo(7)),
    between: S.Int.pipe(S.between(-3, 7)),
    custom: S.Int.pipe(S.filter((x: number) => x !== 3)),
  }
  for (const [name, schema] of Object.entries({int: S.Int, ...filters, branded: S.Int.pipe(S.brand('Count'))})) {
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    console.log(JSON.stringify({version, name, ast: summarize((schema as any).ast)}))
  }
  const accepts = S.is(S.Int)
  console.log(JSON.stringify({version, acceptedIntegers: [-Infinity, Infinity, NaN, 1.5, Number.MIN_SAFE_INTEGER, Number.MAX_SAFE_INTEGER, 2 ** 53, -(2 ** 53), -0].map(value => [String(value), accepts(value)])}))
}
for (const [mod, names] of [['effect', ['function isInt', 'const isInt']], ['effect3', ['const int =', 'Int =', 'IntId']]] as const) {
  const text = readFileSync(`node_modules/${mod}/src/Schema.ts`, 'utf8')
  for (const name of names) { const i = text.indexOf(name); if (i >= 0) console.log(mod, text.slice(Math.max(0, i - 200), i + 1300)) }
}
