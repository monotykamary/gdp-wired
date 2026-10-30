import {readFileSync,writeFileSync} from 'node:fs'
const f=`${import.meta.dir}/cases.json`, c=JSON.parse(readFileSync(f,'utf8')); c.push({id:'p17',lang:'Python',attack:'FastAPI Depends with yielding dependency',pred:'refuted',file:'p17.py'});writeFileSync(f,JSON.stringify(c,null,2))
