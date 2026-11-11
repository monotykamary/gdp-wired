import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
import ts from 'typescript'
function normalized(text:string,erase:boolean){
 const file=ts.createSourceFile('machine.ts',text,ts.ScriptTarget.Latest,true,ts.ScriptKind.TS)
 const result=ts.transform(file,[ctx=>node=>{
  const visit:ts.Visitor=n=>{
   if(ts.isParenthesizedExpression(n))return ts.visitNode(n.expression,visit)
   if(erase&&ts.isCallExpression(n)&&ts.isIdentifier(n.expression)&&n.expression.text==='observeAst'){assert.equal(n.arguments.length,1);return ts.visitNode(n.arguments[0]!,visit)}
   if(erase&&ts.isImportDeclaration(n)&&ts.isStringLiteral(n.moduleSpecifier)&&['./meter.ts','./trace-clock.ts'].includes(n.moduleSpecifier.text))return undefined
   if(erase&&ts.isExpressionStatement(n)&&(n.expression.getText(file).startsWith('coreMeter.')||n.expression.getText(file).startsWith('walk([m.step')&&n.expression.getText(file).includes('stepEvals++')))return undefined
   if(erase&&ts.isVariableStatement(n)&&n.declarationList.declarations.length===1&&n.declarationList.declarations[0]!.name.getText(file)==='stepEvals')return undefined
   if(erase&&ts.isFunctionDeclaration(n)&&['compileE','compileC'].includes(n.name?.text??''))return undefined
   if(erase&&ts.isFunctionDeclaration(n)&&['compileENode','compileCNode'].includes(n.name?.text??''))n=ts.factory.updateFunctionDeclaration(n,[ts.factory.createModifier(ts.SyntaxKind.ExportKeyword)],n.asteriskToken,ts.factory.createIdentifier(n.name!.text.replace('Node','')),n.typeParameters,n.parameters,n.type,n.body)
   if(erase&&ts.isIdentifier(n)&&n.text==='traceNow')return ts.factory.createPropertyAccessExpression(ts.factory.createIdentifier('performance'),'now')
   const out=ts.visitEachChild(n,visit,ctx)
   if(ts.isArrowFunction(out)&&ts.isBlock(out.body)&&out.body.statements.length===1&&ts.isExpressionStatement(out.body.statements[0]!))return ts.factory.updateArrowFunction(out,out.modifiers,out.typeParameters,out.parameters,out.type,out.equalsGreaterThanToken,out.body.statements[0]!.expression)
   return out
  }
  return ts.visitNode(node,visit) as ts.SourceFile
 }])
 try{return ts.createPrinter({removeComments:true}).printFile(result.transformed[0]!)}finally{result.dispose()}
}
const original=normalized(readFileSync(process.argv[2]!,'utf8'),false),current=normalized(readFileSync('core/machine.ts','utf8'),true)
if(original!==current){const a=original.split('\n'),b=current.split('\n'),at=a.findIndex((x,i)=>x!==b[i]);console.error('MACHINE_ERASURE_DIFF',JSON.stringify({line:at+1,before:a.slice(at,at+5),after:b.slice(at,at+5)}))}
assert.equal(current,original,'machine changes must erase to the original algorithm')
console.log('MACHINE_OBSERVATIONS_ERASE_TO_BASE')
