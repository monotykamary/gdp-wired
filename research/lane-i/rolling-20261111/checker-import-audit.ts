import ts from 'typescript'
import {strict as a} from 'node:assert'
import {readFileSync,existsSync} from 'node:fs'
import {resolve,dirname,relative} from 'node:path'
import {createHash} from 'node:crypto'
const root=process.cwd(),seen=new Set<string>(),edges:[string,string][]=[],erased:[string,string][]=[],externals:[string,string][]=[],dynamic:string[]=[]
const visit=(file:string)=>{
 if(seen.has(file))return;seen.add(file)
 const text=readFileSync(resolve(root,file),'utf8'),sf=ts.createSourceFile(file,text,ts.ScriptTarget.Latest,true,ts.ScriptKind.TS)
 const edge=(name:string,types=false)=>{
  if(types){erased.push([file,name]);return}
  if(!name.startsWith('.')){externals.push([file,name]);return}
  let target=resolve(root,dirname(file),name);if(!existsSync(target))target=target.replace(/\.js$/,'.ts')
  a(existsSync(target),'unresolved '+name+' from '+file)
  const child=relative(root,target);edges.push([file,child]);visit(child)
 }
 const walk=(node:ts.Node)=>{
  if(ts.isImportDeclaration(node)&&ts.isStringLiteral(node.moduleSpecifier)){
   const c=node.importClause,b=c?.namedBindings,types=!!c&&(c.isTypeOnly||!c.name&&!!b&&ts.isNamedImports(b)&&b.elements.length>0&&b.elements.every(x=>x.isTypeOnly))
   edge(node.moduleSpecifier.text,types)
  }else if(ts.isExportDeclaration(node)&&node.moduleSpecifier&&ts.isStringLiteral(node.moduleSpecifier)){
   const b=node.exportClause;edge(node.moduleSpecifier.text,node.isTypeOnly||!!b&&ts.isNamedExports(b)&&b.elements.length>0&&b.elements.every(x=>x.isTypeOnly))
  }else if(ts.isCallExpression(node)&&(node.expression.kind===ts.SyntaxKind.ImportKeyword||ts.isIdentifier(node.expression)&&node.expression.text==='require')){
   const arg=node.arguments[0];if(arg&&ts.isStringLiteral(arg))edge(arg.text);else dynamic.push(file+':'+node.pos)
  }
  ts.forEachChild(node,walk)
 };walk(sf)
}
for(const root of ['kernel/kernel.ts','core/check.ts'])visit(root)
a.deepEqual(dynamic,[],'nonliteral dynamic import in checker closure');a.deepEqual(externals,[],'external runtime dependency in checker closure');a(!seen.has('kernel/reader.ts'),'reader reachable from trusted checker imports');a(!seen.has('kernel/prove.ts'),'prover reachable from trusted checker imports')
const files=[...seen].sort().map(file=>({file,sha256:createHash('sha256').update(readFileSync(resolve(root,file))).digest('hex')}))
console.log('CHECKER_RUNTIME_IMPORT_AUDIT '+JSON.stringify({readerReachable:false,proverReachable:false,files,edges,erasedTypeEdges:erased,externalRuntimeImports:externals,nonliteralImports:dynamic}))
