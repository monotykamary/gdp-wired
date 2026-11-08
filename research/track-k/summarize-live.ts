// Read already completed remote receipts; never rerun a proof here.
import assert from 'node:assert/strict'
import {readFileSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
const dir = process.argv[2]!, pairs: any[] = []
for (let run=1;run<=3;run++) {
  let side = ''; const data: Record<string, any> = {}
  for (const line of readFileSync(join(dir,`live-pair-r${run}.log`),'utf8').split('\n')) {
    if (line.startsWith('LIVE begin ')) { side=line.slice(11); data[side]={} }
    if (!line.startsWith('{')) continue
    const row=JSON.parse(line)
    if (row.file) data[side].result=row
    if (row.wallProfile) data[side].profile=row.wallProfile
    if ('liveCuts' in row) data[side].cuts=row
  }
  const {base,cuts}=data
  assert(base?.result && cuts?.result && cuts.cuts?.liveCuts)
  assert.deepEqual(base.result.branches,cuts.result.branches)
  assert.equal(base.result.counted,cuts.result.counted)
  assert(!base.result.complete && !cuts.result.complete)
  assert(base.result.wall<60000 && cuts.result.wall<60000)
  pairs.push({run,baseWallMs:base.result.wall,candidateWallMs:cuts.result.wall,baseCheckMs:base.profile.buckets['final-source-check'].wallMs,candidateCheckMs:cuts.cuts.checkMs,constructionMs:cuts.cuts.buildMs,nodesBefore:cuts.cuts.before,nodesAfter:cuts.cuts.after,mainNodes:cuts.cuts.mainNodes,lemmas:cuts.cuts.cuts,counted:cuts.result.counted,improved:cuts.result.wall<base.result.wall})
}
const summary={pairs,allImproved:pairs.every(p=>p.improved),scope:'isolated send branch, not a complete MLDR proof'}
writeFileSync(join(dir,'comparison.json'),JSON.stringify(summary,null,2)+'\n')
console.log(JSON.stringify(summary,null,2))
