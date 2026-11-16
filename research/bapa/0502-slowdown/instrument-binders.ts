import {readFileSync, writeFileSync} from 'node:fs'

const path = 'core/dsl-binders.ts'
let source = readFileSync(path, 'utf8')
if (source.includes('__GDP_SLOWDOWN_BINDERS__')) process.exit(0)
const prefix = `\n// Diagnostic-only temporary instrumentation; never committed into production source.\ntype __SlowdownBinderMetrics = {calls:number, collectVisits:number, generated:number, groups:number, generatedParts:number, collisionGroups:number, collisionAttempts:number, rewriteVisits:number}\nconst __slowdownBinderMetrics = (): __SlowdownBinderMetrics => {\n  const g = globalThis as unknown as {__GDP_SLOWDOWN_BINDERS__?: __SlowdownBinderMetrics}\n  return g.__GDP_SLOWDOWN_BINDERS__ ??= {calls:0, collectVisits:0, generated:0, groups:0, generatedParts:0, collisionGroups:0, collisionAttempts:0, rewriteVisits:0}\n}\n`
const replace = (from: string, to: string) => { if (!source.includes(from)) throw Error(`instrumentation anchor missing: ${from.slice(0, 48)}`); source = source.replace(from, to) }
replace("const origin = Symbol('generated variable')", prefix + "\nconst origin = Symbol('generated variable')")
replace('export function encodeBinders<T>(value:T,declared:string[],allowedFree:string[]=[]):T {\n  guardReserved(value,allowedFree)', 'export function encodeBinders<T>(value:T,declared:string[],allowedFree:string[]=[]):T {\n  const __m=__slowdownBinderMetrics(); __m.calls++\n  guardReserved(value,allowedFree)')
replace('  const generated=(name:string):boolean=>{\n    const id=identity(name)\n    if(!id)return false', '  const generated=(name:string):boolean=>{\n    __m.generated++\n    const id=identity(name)\n    if(!id)return false')
replace('  const collect=(x:unknown):void=>{\n    if(!x||typeof x!==\'object\')return', '  const collect=(x:unknown):void=>{\n    __m.collectVisits++\n    if(!x||typeof x!==\'object\')return')
replace('  if(!groups.size)return value\n  const names=', '  if(!groups.size)return value\n  __m.groups+=groups.size\n  const names=')
replace('    const suffixes=[...group.parts]\n    let fresh=', '    const suffixes=[...group.parts]; __m.generatedParts+=suffixes.length\n    let fresh=')
replace('    if(suffixes.some(s=>used.has(fresh+s)))do{fresh=`gdp$bound$${++next}`}while(used.has(fresh)||suffixes.some(s=>used.has(fresh+s)))', '    if(suffixes.some(s=>used.has(fresh+s))){__m.collisionGroups++;do{__m.collisionAttempts++;fresh=`gdp$bound$${++next}`}while(used.has(fresh)||suffixes.some(s=>used.has(fresh+s)))}')
replace('  const rewrite=(x:unknown):unknown=>{\n    if(typeof x===\'string\')', '  const rewrite=(x:unknown):unknown=>{\n    __m.rewriteVisits++\n    if(typeof x===\'string\')')
writeFileSync(path, source)
