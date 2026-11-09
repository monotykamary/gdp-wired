// Cause attribution only: this never upgrades an exit to a completed bar run.
export function checkedPortfolioHandoff(view:string,outcome:{exit?:number|null,signal?:string|null,wallMs:number,stages?:any[],resources?:{oomDelta?:number,kernelPidOom?:boolean}}):boolean{
 const stages=outcome.stages??[],answer=stages.at(-1),proof=stages.at(-2),resources=outcome.resources
 return view==='chc'&&(outcome.signal==='SIGKILL'||outcome.exit===137)&&resources?.oomDelta===0&&resources.kernelPidOom===false&&answer?.stage==='answer'&&answer.answer==='sat'&&answer.by==='imc'&&proof?.stage==='imc'&&proof.proven===true&&proof.checked===true&&typeof answer.task==='string'&&answer.task===proof.task&&Number.isFinite(answer.ms)&&proof.ms<=answer.ms&&answer.ms<=outcome.wallMs+100
}
