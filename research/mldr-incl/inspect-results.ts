import {readFileSync} from 'node:fs'
for(const file of process.argv.slice(2))for(const line of readFileSync(file,'utf8').split('\n')){if(!line.startsWith('{'))continue;let row:any;try{row=JSON.parse(line)}catch{continue}if(row.conditional||row.generationOnly){const {data:_data,...result}=row;console.log(JSON.stringify({file,...result}))}}
