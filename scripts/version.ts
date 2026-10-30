// The release's version, set in both packages at once (they release together: gdp-wired-cli is gdp-wired's CLI with
// TypeScript beside it, and depends on gdp-wired at its own version). core/exports.test.ts checks they agree.
//
//   bun scripts/version.ts 0.32.0
import {readFileSync, writeFileSync} from 'node:fs'

const v = process.argv[2] ?? ''
if (!/^\d+\.\d+\.\d+(-[\w.]+)?$/.test(v)) throw new Error(`a version is X.Y.Z: ${JSON.stringify(v)}`)
const root = new URL('../', import.meta.url).pathname
const set = (f: string, edit: (s: string) => string) => writeFileSync(`${root}${f}`, edit(readFileSync(`${root}${f}`, 'utf8')))
set('package.json', s => s.replace(/("version":\s*)"[^"]*"/, `$1"${v}"`))
set('packages/cli/package.json', s => s.replace(/("version":\s*)"[^"]*"/, `$1"${v}"`).replace(/("gdp-wired":\s*)"[^"]*"/, `$1"${v}"`))
console.log(`gdp-wired and gdp-wired-cli at ${v}`)
