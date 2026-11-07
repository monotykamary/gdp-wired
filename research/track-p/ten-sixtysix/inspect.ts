import {readFileSync} from 'node:fs';
const d=JSON.parse(readFileSync('research/track-p/input/family.json','utf8'));
for(const i of [2,3,4,7,9,10,11,13,14,17,33,45,61,64,66,70,71,73,74]) console.log('LAW',i,JSON.stringify(d.laws[i],null,2));
console.log('MACHINE',JSON.stringify(d.machine,null,2));
