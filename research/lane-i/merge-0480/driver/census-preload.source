// Independent research tripwire: loaded before source imports, counts reads even
// if an untrusted search catches the thrown error. Not part of proof authority.
const gate={active:false,reads:0}
;(globalThis as unknown as {commonCensusClock:typeof gate}).commonCensusClock=gate
const date=Date.now.bind(Date),performanceNow=performance.now.bind(performance)
function checked(read:()=>number):number{if(gate.active){gate.reads++;throw Error('census counted-scope wall read')}return read()}
Date.now=()=>checked(date)
Object.defineProperty(performance,'now',{configurable:true,writable:true,value:()=>checked(performanceNow)})
