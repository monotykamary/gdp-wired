// Scheduling hints only. Every selected strategy must still prove its result.
import {type C, type E, type Machine, n, same, walkOnce, x} from './machine.ts'
import {type RowAgreementShape} from './row-agreement-shape.ts'
import {countFrameConditions, fixedCountFrameCase} from './count-frames.ts'
import {type Path, canon, cellParts, isCell, linear, substC, truth} from '../kernel/kernel.ts'
export function classifyRowValueWrite(m: Machine, row: Pick<RowAgreementShape, 'map' | 'fields'>): 'load' | 'replacement' | undefined {
  const choice = fixedCountFrameCase(m)
  if (!choice) return
  const path: Path = new Map(countFrameConditions(choice).map(lin => [canon(lin), {lin, holds: true}]))
  // A scheduling-only evaluation: the checked proof still receives the original machine.
  const vars = {[choice.name]: n(choice.value)}, flags: Record<string, C> = Object.create(null)
  for (const [name, c] of Object.entries(m.step.flags ?? {})) flags[name] = c.op === 'all' ? same(x('?' + name), n(1)) : substC(c, {vars, maps: {}, flags})
  const foreignRead = (value: E | C): boolean => {
    let loaded = false
    walkOnce(value, (node: any) => {if (node.op === 'get' && node.map !== row.map && Object.hasOwn(m.maps ?? {}, node.map)) loaded = true})
    return loaded
  }
  // Boolean maps compile data selection into the condition of a 1/0 indicator.
  // Ignore decided Boolean branches before looking for a data-source read.
  const unresolvedRead = (c: C, match: (value: C) => boolean): boolean => {
    if (truth(c, path) !== undefined) return false
    if (c.op === 'and' || c.op === 'or') return c.xs.some(child => unresolvedRead(child, match))
    if (c.op === 'not') return unresolvedRead(c.x, match)
    return match(c)
  }
  const active = (e: E, predicate: (e: E) => boolean, indicatorReads = false, indicatorMatch: (value: C) => boolean = foreignRead): boolean => {
    if (e.op !== 'if') return predicate(e)
    const condition = substC(e.c, {vars, maps: {}, flags}), known = truth(condition, path)
    const indicator = e.then.op === 'const' && e.else.op === 'const' && e.then.value !== e.else.value && [0, 1].includes(e.then.value) && [0, 1].includes(e.else.value)
    return indicatorReads && indicator && unresolvedRead(condition, indicatorMatch) || known !== false && active(e.then, predicate, indicatorReads, indicatorMatch) || known !== true && active(e.else, predicate, indicatorReads, indicatorMatch)
  }
  for (const field of row.fields) {
    const write = m.step.maps?.[field]
    if (!write || !('each' in write)) continue
    if (active(write.value, e => {
      const value = linear(e, path), terms = value && Object.entries(value).filter(([name, k]) => name !== '1' && k !== 0)
      return !!value && value['1'] === 1 && terms?.length === 1 && terms[0]![1] === 1 && isCell(terms[0]![0]) && cellParts(terms[0]![0]).map === field
    })) return 'replacement'
  }
  const write = m.step.maps?.[row.map]
  if (!write) return
  const carriedRead = (value: E | C): boolean => {let carried = false; walkOnce(value, (node: any) => {if (node.op === 'get' && m.inputMaps?.includes(node.map)) carried = true}); return carried}
  if (active(write.value, carriedRead, true, carriedRead)) return 'replacement'
  return active(write.value, foreignRead, true) ? 'load' : undefined
}
