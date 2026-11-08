import {readFileSync} from 'node:fs';
import {countedObligations} from '../../../kernel/kernel.ts';
const {machine:m,laws}=JSON.parse(readFileSync('research/track-p/input/family.json','utf8'));
const ids=[2,3,4,7,9,10,11,13,14,17,33,45,61,64,66,70,71,73,74];
console.log(JSON.stringify({laws:ids.map(i=>({i,...laws[i]})),machine:m,raw:countedObligations(m,ids.map(i=>laws[i]),{},ids.indexOf(33))[1]}));
