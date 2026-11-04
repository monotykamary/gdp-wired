// Runs in a FRESH process only after the builtin bootstrap has exited successfully.
import ts from 'typescript'
import {checkDocument} from '../../../interchange/check.ts'
import {extractPython} from '../../../core/extract-py.ts'
import {writeSync,realpathSync} from 'node:fs'
import {createRequire} from 'node:module'
import {resolve} from 'node:path'
const actual=realpathSync(createRequire(import.meta.url).resolve('typescript'))
if(actual!==realpathSync(resolve('node_modules/typescript/lib/typescript.js'))||realpathSync(process.cwd())!==realpathSync(process.env.LIFECYCLE_STAGE!)||ts.version!=='5.9.3'||typeof checkDocument!=='function'||typeof extractPython!=='function')throw Error('fresh import closure mismatch')
const b=Buffer.from('V3_BOUNDARY '+JSON.stringify({event:'load-complete',data:{typescriptVersion:ts.version,privateResolution:true,checkerLoaded:true,extractorLoaded:true}})+'\n');let i=0;while(i<b.length)i+=writeSync(1,b.subarray(i))
