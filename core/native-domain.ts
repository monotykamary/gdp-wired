// Read native argument domains from TypeScript's types, independently of symbolic
// input variables/heap identities. Capture the actual parameter bindings at entry,
// after JS defaults and destructuring, rather than rebuilding them from the model.
import ts from 'typescript'
import {normalize, program, scriptKind} from './extract-read.ts'
export type NativeInputs = {domains?: unknown[][], reason?: string}
const LIMIT = 65536
class TooLarge extends Error {}
function named(n: ts.Node): string | undefined {
  if (ts.isFunctionDeclaration(n) || ts.isMethodDeclaration(n)) return n.name && (ts.isIdentifier(n.name) || ts.isStringLiteral(n.name)) ? n.name.text : undefined
  if (ts.isArrowFunction(n) || ts.isFunctionExpression(n)) {
    const p = n.parent
    if ((ts.isVariableDeclaration(p) || ts.isPropertyAssignment(p)) && (ts.isIdentifier(p.name) || ts.isStringLiteral(p.name))) return p.name.text
  }
  return undefined
}
const callable = (n: ts.Node): n is ts.FunctionDeclaration | ts.MethodDeclaration | ts.ArrowFunction | ts.FunctionExpression => ts.isFunctionDeclaration(n) || ts.isMethodDeclaration(n) || ts.isArrowFunction(n) || ts.isFunctionExpression(n)
function bindingNames(name: ts.BindingName): string[] {
  return ts.isIdentifier(name) ? [name.text] : name.elements.flatMap(e => ts.isOmittedExpression(e) ? [] : bindingNames(e.name))
}
export function nativeCaptureEdits(code: string, file: string, methods: string[]): [number, string][] {
  if (!methods.length) return []
  const sf = ts.createSourceFile(file, code, ts.ScriptTarget.ES2022, true, scriptKind(file)), edits: [number, string][] = []
  const visit = (n: ts.Node) => {
    if (callable(n) && n.body && methods.includes(named(n) ?? '')) {
      const names = n.parameters.flatMap(p => bindingNames(p.name)), capture = `__gdp_native_capture(${JSON.stringify(named(n))}, {${names.join(',')}})`
      if (ts.isBlock(n.body)) edits.push([n.body.getStart(sf) + 1, `${capture};`])
      else edits.push([n.body.getStart(sf), `(${capture}, (`], [n.body.end, '))'])
    }
    ts.forEachChild(n, visit)
  }
  visit(sf)
  return edits
}
export function nativeInputs(code: string, file: string, entry: string, files: Record<string, string> = {}): NativeInputs {
  const root = file.slice(0, file.length - (file.split('/').pop()!.length))
  const extra = Object.fromEntries(Object.entries(files).map(([name, text]) => [normalize(`${root}${name}`), text]))
  const {sf, checker} = program(code, file, extra)
  let target: ts.FunctionDeclaration | ts.MethodDeclaration | ts.ArrowFunction | ts.FunctionExpression | undefined
  const visit = (n: ts.Node) => { if (callable(n) && named(n) === entry) target ??= n; ts.forEachChild(n, visit) }
  visit(sf)
  if (!target) return {reason: 'native entry signature could not be read independently'}
  const domain = (t: ts.Type, depth = 0): unknown[] | undefined => {
    if (depth > 12) return undefined
    if (t.isUnion()) {
      const parts = t.types.map(x => domain(x, depth + 1))
      if (parts.some(x => x === undefined)) return undefined
      const out = parts.flat()!; if (out.length > LIMIT) throw new TooLarge(); return out
    }
    if (t.flags & ts.TypeFlags.BooleanLiteral) return [(t as ts.Type & {intrinsicName: string}).intrinsicName === 'true']
    if (t.flags & ts.TypeFlags.Boolean) return [false, true]
    if (t.isStringLiteral() || t.isNumberLiteral()) return [t.value]
    if (t.flags & ts.TypeFlags.Undefined || t.flags & ts.TypeFlags.Void) return [undefined]
    if (t.flags & ts.TypeFlags.Null) return [null]
    if (t.flags & ts.TypeFlags.Never) return []
    if (!(t.flags & ts.TypeFlags.Object) || checker.getIndexInfosOfType(t).length || t.getCallSignatures().length || t.getConstructSignatures().length) return undefined
    let rows: Record<string, unknown>[] = [{}]
    for (const p of t.getProperties()) {
      const at = p.valueDeclaration ?? p.declarations?.[0]
      if (!at) return undefined
      const values = domain(checker.getTypeOfSymbolAtLocation(p, at), depth + 1)
      if (!values) return undefined
      const optional = !!(p.flags & ts.SymbolFlags.Optional), factor = values.length + Number(optional)
      if (rows.length * factor > LIMIT) throw new TooLarge()
      rows = rows.flatMap(row => [...(optional ? [row] : []), ...values.map(value => ({...row, [p.name]: value}))])
    }
    return rows
  }
  try {
    const domains: unknown[][] = []
    let size = 1
    for (const p of target.parameters) {
      if (p.dotDotDotToken) return {reason: 'native rest-argument domain is not supported'}
      const values = domain(checker.getTypeAtLocation(p))
      if (!values) return {}
      if ((p.questionToken || p.initializer) && !values.includes(undefined)) values.push(undefined)
      size *= values.length
      if (size > LIMIT) throw new TooLarge()
      domains.push(values)
    }
    return {domains}
  } catch (e) {
    if (e instanceof TooLarge) return {reason: `finite native domain exceeds the exhaustive bound of ${LIMIT}; no sampled proof is substituted`}
    return {reason: `native input domains unavailable: ${e instanceof Error ? e.message : String(e)}`}
  }
}
