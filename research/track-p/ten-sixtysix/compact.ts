import {readFileSync} from 'node:fs';
import {countedObligations} from '../../../kernel/kernel.ts';
const d=JSON.parse(readFileSync('research/track-p/input/family.json','utf8')),m=d.machine;
function pp(e:any):string{if(e===null||typeof e!=='object')return String(e);if(Array.isArray(e))return '['+e.map(pp).join(', ')+']';if(!e.op)return '{'+Object.entries(e).map(([k,v])=>k+': '+pp(v)).join(',\n')+'}';switch(e.op){case 'const':return ''+e.value;case 'var':return e.name;case 'get':return e.map+'['+pp(e.key)+']';case 'flag':return e.name;case 'and':case 'or':return '('+e.xs.map(pp).join(' '+e.op+' ')+')';case 'not':return '!'+pp(e.x);case 'mul':return '('+e.k+'*'+pp(e.a)+')';case 'if':return 'if '+pp(e.c)+' then '+pp(e.t)+' else '+pp(e.e);default:return JSON.stringify(e);}}
const ids=[2,3,4,7,9,10,11,13,14,17,33,45,61,64,66,70,71,73,74],ls=ids.map(i=>d.laws[i]);
for(const i of ids)console.log('LAW',i,pp(d.laws[i]));
for(const key of ['counts','step'])console.log('MACHINE',key,pp(m[key]));
for(const i of [10,66])console.log('RAW',i,pp(countedObligations(m,ls,{},ids.indexOf(i))[1]));
