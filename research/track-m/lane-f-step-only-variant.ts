// Disposable STEP-only, full-family replay. No deadline or selection changes.
import {readFileSync,writeFileSync,renameSync} from 'node:fs'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux required')
const file='core/counts.ts',source=readFileSync(file,'utf8')
const old="const obligations = (i: Instances) => ptime('encode', () => countedObligations(m, ls, {[law.name]: i}, ls.indexOf(law)))"
const contexts=source.split('\n').find(l=>l.trim().startsWith('const contexts = '))
const focused=source.split('\n').find(l=>l.trim().startsWith('const focused = pass'))
if(source.split(old).length!==2||!contexts||!focused||source.split(contexts).length!==2||source.split(focused).length!==2)throw Error('STEP replay anchors changed')
const next=source.replace(old,"const obligations = (i: Instances) => ptime('encode', () => countedObligations(m, ls, {[law.name]: i}, ls.indexOf(law)).filter(({goal}) => goal.name.endsWith('@step')))")
 .replace(contexts,'      const contexts: {local: Law[], fraction: number, kind: string}[] = [] // diagnostic: full retained family only')
 .replace('relevantGoals, relevantLaws','relevantGoals')
 .replace(focused,focused.replace('const focused =','const _focused ='))
writeFileSync(file+'.tmp',next);renameSync(file+'.tmp',file)
