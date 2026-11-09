// Check reported sampled maxima against retained samples and the terminal marker.
type Telemetry={peakRssKiB?:number,samples?:{rssKiB:number}[]}
export function validPeakRss(resource:Telemetry,end:{peakRssKiB?:number}|undefined):boolean{
 const samples=resource.samples??[]
 return samples.length>0&&samples.every(s=>Number.isFinite(s.rssKiB)&&s.rssKiB>=0)&&Number.isFinite(resource.peakRssKiB)&&resource.peakRssKiB===Math.max(...samples.map(s=>s.rssKiB))&&resource.peakRssKiB===end?.peakRssKiB
}
