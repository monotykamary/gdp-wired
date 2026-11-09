// Pure integrity checks; no timing assertion can substitute for equal proof work.
export type IntegrityLaw={law:string,proven:boolean,checked:boolean,wallMs:number,kernelMs:number,countedUnits:number,sites:Record<string,{calls:number}>}
export type IntegrityRun={id:string,variant:string,exitCode?:number,skipped?:string,laws:IntegrityLaw[]}
export type IntegritySource={productionDifferences:string[],installedProductionDifferences:string[]}
export function auditIntegrity(runs:IntegrityRun[],source:IntegritySource){
 if(source.productionDifferences.length||source.installedProductionDifferences.length)throw new Error('source mismatch')
 const first=runs.find(r=>!r.skipped)
 if(!first)throw new Error('no completed controls')
 const counts=(l:IntegrityLaw)=>JSON.stringify(Object.entries(l.sites).map(([k,v])=>[k,v.calls]).sort(([a],[b])=>String(a).localeCompare(String(b))))
 const comparisons=[]
 for(const r of runs.filter(r=>!r.skipped)){
  if(r.exitCode!==0||r.laws.length!==3||!r.laws.every(l=>l.checked&&l.proven&&Number.isFinite(l.countedUnits)))throw new Error('unchecked/incomplete '+r.id)
  for(const [i,l]of r.laws.entries()){
   const base=first.laws[i]!
   if(l.law!==base.law||l.countedUnits!==base.countedUnits)throw new Error('different proof work '+r.id+' '+l.law)
   if(!r.variant.endsWith('-plain')&&counts(l)!==counts(base))throw new Error('different call counts '+r.id+' '+l.law)
   comparisons.push({id:r.id,variant:r.variant,law:l.law,wallMs:l.wallMs,kernelMs:l.kernelMs,countedUnits:l.countedUnits,kernelRatioToA1:base.kernelMs?l.kernelMs/base.kernelMs:null,rootChecks:l.sites['kernel/kernel.ts:checkMC']?.calls??null})
  }
 }
 return comparisons
}
