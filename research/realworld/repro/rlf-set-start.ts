// Repro: rate-limiter-flexible 11.2.3 (npm; tag v11.2.3 = d19a457455338b73172d47d004f402bd0b748152), the run that refuted
// the first statement of the RateLimiterMemory safety law ("start + admitted <= points + rewarded"): params {points: 0,
// duration: 0}, `consume('2', 0)` then `set('3', 2, 0)`. The code makes key 3's record with value 2, above points 0,
// and lets nothing through: the start value may pass the limit, so the law (not the code) overstated it.
//   bun research/realworld/repro/rlf-set-start.ts                     (needs npm)
import {execFileSync} from 'node:child_process'
import {mkdtempSync} from 'node:fs'
import {createRequire} from 'node:module'
import {tmpdir} from 'node:os'
import {join} from 'node:path'

const dir = mkdtempSync(join(tmpdir(), 'rlf-repro-'))
execFileSync('npm', ['install', '--prefix', dir, '--no-audit', '--no-fund', '--silent', 'rate-limiter-flexible@11.2.3'], {stdio: 'inherit'})
const {RateLimiterMemory} = createRequire(join(dir, 'x.js'))('rate-limiter-flexible') as {RateLimiterMemory: new (o: object) => any}
const lim = new RateLimiterMemory({points: 0, duration: 0})
console.log('consume(2, 0):', await lim.consume(2, 0).then(() => 'let through', () => 'refused'))
await lim.set(3, 2, 0)
console.log('after set(3, 2, 0), get(3):', JSON.stringify(await lim.get(3)))
console.log('consume(3, 0):', await lim.consume(3, 0).then(() => 'let through', () => 'refused'))
