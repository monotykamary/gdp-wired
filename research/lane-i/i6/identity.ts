import {strict as a} from 'node:assert'
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import ts from 'typescript'
const observers=new Set(['observeCheckStep','observeTableCells','observeLinearRows','observeConstraintRows','observeCubeTest'])
const observed=(n:ts.Node):boolean=>ts.isCallExpression(n)&&ts.isIdentifier(n.expression)&&observers.has(n.expression.text)
function normalize(text:string,erase:boolean){
 const source=ts.createSourceFile('source.ts',text,ts.ScriptTarget.Latest,true,ts.ScriptKind.TS)
 const result=ts.transform(source,[context=>root=>{
  const visit:ts.Visitor=node=>{
   if(ts.isParenthesizedExpression(node))return ts.visitNode(node.expression,visit)
   if(erase&&ts.isImportDeclaration(node)&&node.importClause?.namedBindings&&ts.isNamedImports(node.importClause.namedBindings)&&node.importClause.namedBindings.elements.every(x=>observers.has(x.name.text)))return undefined
   if(erase&&ts.isExpressionStatement(node)&&observed(node.expression))return undefined
   if(erase&&ts.isBinaryExpression(node)&&node.operatorToken.kind===ts.SyntaxKind.CommaToken&&observed(node.left))return ts.visitNode(node.right,visit)
   return ts.visitEachChild(node,visit,context)
  }
  return ts.visitNode(root,visit) as ts.SourceFile
 }])
 try{return ts.createPrinter({removeComments:true}).printFile(result.transformed[0]!)}finally{result.dispose()}
}
const [before,after]=process.argv.slice(2)
for(const path of ['core/check.ts','kernel/kernel.ts','core/infer.ts']){
 const original=normalize(readFileSync(join(before!,path),'utf8'),false),current=normalize(readFileSync(join(after!,path),'utf8'),true)
 if(original!==current){const x=original.split('\n'),y=current.split('\n'),at=x.findIndex((line,i)=>line!==y[i]);console.error('I6_ERASURE_DIFF',JSON.stringify({path,line:at+1,original:x.slice(at,at+5),current:y.slice(at,at+5)}))}
 a.equal(current,original,path+' changes must erase to the original algorithm')
 console.log('I6_ERASURE_IDENTICAL '+path)
}
