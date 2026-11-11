// Scheduling only: a single per-law grant inside the existing root/search
// horizon. A later citation/model never renews a previously issued grant.
export function countReachabilityAllowance(root:number,ordinary:number,citing:number):number{
 if([root,ordinary,citing].some(x=>!Number.isFinite(x)||x<0))throw new RangeError('invalid reachability allowance')
 return Math.min(root/20,Math.max(root/1000,Math.max(ordinary,citing)*3/20))
}
