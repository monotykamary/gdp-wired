// Minimal, owned positive controls. Historical runs must use these sources without
// applying the corresponding extractor/law fixes to the parent or released reader.
export type SourceControl = {id: string, revision: string, source: string, entry: string, standalone: boolean, expr: string, args: unknown[], writes?: [string, unknown][], holds: (result: unknown, args: unknown[]) => boolean}
export const sourceControls: SourceControl[] = [
  {id: 'B1', revision: '8214a543', entry: 'Decision', standalone: false,
    source: 'export class Decision { values = new Map<string, number>(); decide(key: string): number | undefined { return this.values.get(key); } }',
    expr: 'result is undefined implies result - 0 <= 1 business days', args: ['a'], holds: result => typeof result === 'number' && Number.isFinite(result)},
  {id: 'B2', revision: 'dd5ee124', entry: 'Decision', standalone: false,
    source: 'export class Decision { values = new Map<string, boolean>(); put(key: string, value: boolean) { this.values.set(key, value); } decide(key: string): boolean { const value = this.values.get(key); if (!value) return value === undefined; return true; } }',
    expr: 'result == true', args: ['a'], writes: [['a', false]], holds: result => result === true},
  {id: 'P1', revision: '4497c4b0', entry: 'decide', standalone: true,
    source: 'export function decide(a: "red"): "green" { return "green"; }',
    expr: 'result == a', args: ['red'], holds: (result, args) => result === args[0]},
  {id: 'P2', revision: '69401de0', entry: 'decide', standalone: true,
    source: 'export function decide(arg: {enabled: boolean}, {enabled}: {enabled: boolean}): boolean { return arg.enabled; }',
    expr: 'result == enabled', args: [{enabled: false}, {enabled: true}], holds: (result, args) => result === (args[1] as {enabled: boolean}).enabled},
  {id: 'Map.get-0.47.0', revision: '0.47.0', entry: 'Decision', standalone: false,
    source: 'export class Decision { flags = new Map<string, boolean>(); decide(key: string): boolean { const flag = this.flags.get(key); if (flag !== null) return flag === undefined; return false; } }',
    expr: 'result == false', args: ['a'], holds: result => result === false},
]
export function nativeCounterexample(c: SourceControl): {args: unknown[], result: unknown} {
  const js = new Bun.Transpiler({loader: 'ts'}).transformSync(c.source).replace(/export\s+(?=function|class)/g, '')
  // Only the constant, owned sources above are executable; no external/generated answer is loaded.
  // oxlint-disable-next-line typescript/no-implied-eval
  const target = new Function(`${js}; return ${c.entry};`)() as ((...args: unknown[]) => unknown) | (new () => {put?: (key: string, value: unknown) => void, decide: (...args: unknown[]) => unknown})
  if (c.standalone) return {args: c.args, result: (target as (...args: unknown[]) => unknown)(...c.args)}
  const object = new (target as new () => {put?: (key: string, value: unknown) => void, decide: (...args: unknown[]) => unknown})()
  for (const [key, value] of c.writes ?? []) object.put!(key, value)
  return {args: c.args, result: object.decide(...c.args)}
}
