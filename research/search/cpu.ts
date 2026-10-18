// The same enumeration on one CPU thread (the generated JS), and the interpreter's shortest-first search at its default
// depth, for comparison.
import {search} from '../../core/machine.ts'
import {NONE, js, size} from './compile.ts'
import {searches} from './models.ts'
for (const s of searches) {
  const f = js(s.m, s.law, s.space), total = size(s.m, s.space)
  const started = performance.now()
  let best: {depth: number, index: number} | undefined
  for (let index = 0; index < total; index++) {
    const depth = f(index)
    if (depth !== NONE && (!best || depth < best.depth)) best = {depth, index}
  }
  const ms = performance.now() - started
  const t0 = performance.now(), shallow = search(s.m, s.law), shallowMs = performance.now() - t0
  console.log(JSON.stringify({what: s.what, candidates: total, jsMs: Math.round(ms), best, defaultSearch: shallow ? `found at depth ${shallow.trace.length}` : 'nothing within depth 3', defaultMs: Math.round(shallowMs)}))
}
