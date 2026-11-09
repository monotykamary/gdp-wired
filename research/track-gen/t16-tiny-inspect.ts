import {readFileSync} from 'node:fs'
import {mldr} from '../protocols/ic3syn/mldr.ts'
const c=JSON.parse(readFileSync('tiny-data/0.json','utf8'))
const r=mldr(); console.log('SOURCE',JSON.stringify(r.machine)); console.log('CAPTURE KEYS',Object.keys(c)); console.log('FAMILY',JSON.stringify(c.beforeFinite??c))
