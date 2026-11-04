import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import type {Law} from '../../../core/machine.ts'
const wrapper=JSON.parse(readFileSync('research/egraph/historical/inputs/gdp-wired-laneQ3/core/fixtures/published-ground/paxos-P5-19.json','utf8')) as {data:string}
const p=JSON.parse(gunzipSync(Buffer.from(wrapper.data,'base64')).toString()) as {laws:Law[],witness:Record<string,number>,gg:{name:string,hyps:unknown[]}}
console.log('Q3_DETAIL',JSON.stringify({laws:p.laws.map(l=>l.name),voteLaw:p.laws.filter(l=>/vote.*propos/i.test(l.name)),cells:Object.entries(p.witness).filter(([k])=>/Vote|Proposal/.test(k)),goal:p.gg.name,hyps:p.gg.hyps.length}))
