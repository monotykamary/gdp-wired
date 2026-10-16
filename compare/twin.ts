// gdp-wired's optional Lean twin on exactly the three compared rules (compare/domain.ts): the TypeScript kernel's trees
// as Lean data, each checked by lean-kernel/'s Kern.machine_sound, fmmachine_sound and hmachine_sound with
// `decide +kernel`, through export-kernel.ts --examples. `bun compare/twin.ts > Compare.lean`, then `lean Compare.lean`
// with LEAN_PATH holding lean-kernel/ and its History.olean built (compare/modal_compare.py does both on Modal).
import {resolve} from 'node:path'

const dir = resolve(import.meta.dir, '..', 'lean-kernel')
const p = Bun.spawnSync(['bun', 'export-kernel.ts', '--examples', '../compare/domain.ts'], {cwd: dir, stdout: 'pipe', stderr: 'pipe'})
process.stdout.write(p.stdout)
process.stderr.write(p.stderr)
process.exitCode = p.exitCode ?? 1
