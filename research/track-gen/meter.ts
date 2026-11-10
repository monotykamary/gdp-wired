// Research-only attribution. Installed in disposable snapshots, never imported by production.
import type {Law} from '../../core/machine.ts'
export const families: Record<string, {calls: number, ms: number, laws: Law[]}> = {}
export function measure<T>(name: string, f: () => T): T {
  const start = performance.now()
  const value = f(), item = families[name] ??= {calls: 0, ms: 0, laws: []}
  item.calls++; item.ms += performance.now() - start
  if (Array.isArray(value)) item.laws.push(...value.filter((x): x is Law => !!x?.holds && typeof x.name === 'string'))
  return value
}
