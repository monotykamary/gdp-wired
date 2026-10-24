// A preload: each root query slower than $GDP_SLOW_MS (1000) written out, its goal as research/dag/goalio.ts's JSON, to
// $GDP_SLOW_DIR/<n>.json (for replaying it alone: research/step/goal.ts). Research tooling.
import {mkdirSync, writeFileSync} from 'node:fs'
import {queryHook} from '../../kernel/prove.ts'
import {dumpGoal} from '../dag/goalio.ts'

const dir = process.env.GDP_SLOW_DIR, ms = Number(process.env.GDP_SLOW_MS ?? 1000)
if (dir) {
  mkdirSync(dir, {recursive: true})
  let n = 0
  const was = queryHook.on
  queryHook.on = q => { was?.(q); if (q.ms > ms) writeFileSync(`${dir}/${process.pid}-${n++}.json`, dumpGoal(q.goal)) }
}
