// Observation only: never a budget, proof, or authorization. No clock is read
// without an observer. Native checks remain in their original call sites.
import {fullRate, fullWork} from '../kernel/prove.ts'
import {traceNow} from './trace-clock.ts'
export type CountStageRole = 'untrusted-assembly' | 'untrusted-search' | 'trusted-check'
export type CountStageObserver = (event: Record<string, unknown>) => void
export function countStageTrace(observe?: CountStageObserver, total?: string) {
  const now = () => ({wall: traceNow(), work: fullWork()})
  const begin = observe ? now() : undefined
  let current: {part: string, role: CountStageRole, value?: number, at: ReturnType<typeof now>} | undefined, finished = false
  const close = () => {
    if (!observe || !current) return
    const end = now(), {part, role, value, at} = current
    current = undefined
    observe({stage: 'tail', part, role, ...(value === undefined ? {} : {value}), wallMs: end.wall - at.wall, units: (end.work - at.work) / fullRate})
  }
  return {
    mark(part: string, role: CountStageRole, value?: number) {
      if (!observe || finished) return
      close(); current = {part, role, value, at: now()}
    },
    pause: close,
    finish() {
      if (finished) return
      finished = true; close()
      if (!observe || !begin || !total) return
      const end = now()
      observe({stage: 'tail', part: total, aggregate: true, wallMs: end.wall - begin.wall, units: (end.work - begin.work) / fullRate})
    }
  }
}
export function traceCountStage<T>(observe: CountStageObserver | undefined, part: string, role: CountStageRole, run: () => T): T {
  const trace = countStageTrace(observe)
  trace.mark(part, role)
  try {return run()} finally {trace.finish()}
}
