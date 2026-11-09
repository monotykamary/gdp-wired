const allowed = new Set(['AMD EPYC 9455 48-Core Processor','AMD Ryzen 9 9950X 16-Core Processor'])
export function selectPaxosCpu(value?:string):string {
 const cpu=value??'AMD EPYC 9455 48-Core Processor'
 if(cpu!=='any'&&!allowed.has(cpu))throw new Error('unsupported Paxos timing CPU: '+cpu)
 return cpu
}
export const paxosCpu=selectPaxosCpu(process.env.PAXOS_TARGET_CPU)
