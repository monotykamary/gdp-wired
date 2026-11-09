import {countsDump} from '../../core/counts.ts'
const prior=countsDump.on
countsDump.on=(d:any)=>{prior?.(d);if(d.phase==='member-premises')console.log(JSON.stringify({memberPremises:true,...d}))}
