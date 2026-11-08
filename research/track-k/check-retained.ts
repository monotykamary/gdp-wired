// Authenticate unchanged retained certificates with the current kernel; never import a prover.
import assert from 'node:assert/strict'
import {createHash} from 'node:crypto'
import {readFileSync} from 'node:fs'
import {type CountCert, type CountDecl, type Goal, checkMC} from '../../kernel/kernel.ts'
import {costs, work} from '../../core/solver.ts'
const pins: Record<string, [string, string]> = {
  c14: ['9f47e6f4f62e621b26f12600a2854a30e1815ccd6e042ed4a50b44de78ed61e2', '137d8494c50f998fd6387df6eb03f8a5650aa1b6bb37228be0fe7542ae8be72a'],
  c9: ['96693f267b1dfa17ce76caf30754d552df7804425c845bdf81aa05d25ba6082d', '4e95c0afde042e383f494f8d52b4b1c40e505443ed2db9e5e9dabccba8a12eed'],
  c11: ['97612173ae500bd2101a4220bcefadfc8201be22cb5146edb79c4e29f5bcb2fd', 'fbcd3bfd428be99ea8ed5307226a55739d873a61ef3186571e74eeb108ad5134'],
}
const [root, id] = process.argv.slice(2) as [string, string]
const sha = (s: string) => createHash('sha256').update(s).digest('hex')
const gb = readFileSync(`${root}/${id}/goal.json`, 'utf8'), pb = readFileSync(`${root}/${id}/proof.json`, 'utf8')
assert.equal(sha(gb), pins[id]?.[0]); assert.equal(sha(pb), pins[id]?.[1])
const pack = JSON.parse(gb) as {raw: Goal, decls: CountDecl[]}, cert = JSON.parse(pb) as CountCert
assert(!Object.hasOwn(cert, 'lemmas'))
assert.equal(work.n, 0)
assert(Object.values(costs).every(n => n === 0))
const started = performance.now(), checked = checkMC(pack.raw.hyps, pack.decls, cert)
const emptyChecked = checkMC(pack.raw.hyps, pack.decls, {...cert, lemmas: []})
assert(checked && emptyChecked)
assert.equal(work.n, 0)
assert(Object.values(costs).every(n => n === 0))
console.log(JSON.stringify({id, checked, emptyChecked, ms: performance.now() - started, searchWork: work.n, goalSHA256: sha(gb), proofSHA256: sha(pb)}))
