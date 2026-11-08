// Apply the untrusted sharing experiment to an already recorded Track M snapshot, never its worktree.
import {createHash} from 'node:crypto'
import {copyFileSync, readFileSync, writeFileSync} from 'node:fs'
import {join, resolve} from 'node:path'
const root = resolve(import.meta.dir, '../..'), input = resolve(process.argv[2]!), snapshot = join(input, 'snapshot')
const read = (p: string) => readFileSync(p, 'utf8')
const swap = (text: string, old: string, next: string) => {
  if (text.includes(next)) return text
  if (!text.includes(old)) throw Error(`Missing snapshot anchor: ${old.slice(0, 90)}`)
  return text.replace(old, next)
}
for (const [from,to] of [['core/lemma-cuts.ts','core/lemma-cuts.ts'],['kernel/kernel.ts','kernel/kernel.ts'],['research/track-k/lemma-origin-dump.ts','research/track-m/lemma-origin-dump.ts']]) copyFileSync(join(root,from!),join(snapshot,to!))
const current = read(join(root,'kernel/prove.ts')), start = current.indexOf('export function widen('), marker = '\n// Whether each hypothesis reads only names the goal', end = current.indexOf(marker,start)
if (start < 0 || end < 0) throw Error('No row-aware widen in current proposer')
let prover = read(join(snapshot,'kernel/prove.ts'))
const a = prover.indexOf('export function widen('), b = prover.indexOf(marker,a)
if (a < 0 || b < 0) throw Error('No compatible widen in recorded snapshot')
prover = prover.slice(0,a) + current.slice(start,end) + prover.slice(b)
prover = prover.replace("import {proofOrigins, rememberProofOrigin} from '../core/lemma-cuts.ts'", "import {rememberProofRows} from '../core/lemma-cuts.ts'")
prover = swap(prover, '// A tree for a weaker goal (some hypotheses left out, some conjuncts of one left out)', "import {rememberProofRows} from '../core/lemma-cuts.ts'\n\n// A tree for a weaker goal (some hypotheses left out, some conjuncts of one left out)")
writeFileSync(join(snapshot,'kernel/prove.ts'),prover)
let replay = read(join(snapshot,'research/track-m/count-case-replay.ts'))
replay = swap(replay, "import {readFileSync} from 'node:fs'", "import {readFileSync} from 'node:fs'\nimport {lemmaPack} from './lemma-origin-dump.ts'")
replay = swap(replay, "import {lemmaPack} from './lemma-origin-dump.ts'", "import {lemmaPack} from './lemma-origin-dump.ts'\nimport {shareLemmaCuts} from '../../core/lemma-cuts.ts'")
if (!replay.includes('brotliCompressSync, constants as zlibConstants')) replay = swap(replay, "import {readFileSync} from 'node:fs'", "import {readFileSync} from 'node:fs'\nimport {brotliCompressSync, constants as zlibConstants} from 'node:zlib'")
replay = swap(replay, 'modelInstances,withDeadline,withWall}', 'modelInstances,wallAt,withDeadline,withWall}')
const packLine = "  if(process.env.LAB_DUMP_PROOF==='1')console.log('PACKBR '+brotliCompressSync(Buffer.from(JSON.stringify(lemmaPack({goal,tree:t,path:[...branchRoots[i]!],raw:base.goal,decls:base.decls,cert}))),{params:{[zlibConstants.BROTLI_PARAM_QUALITY]:5}}).toString('base64'))"
if (!replay.includes("console.log('PACKBR '")) replay = swap(replay, '  return check(goal,t,branchRoots[i]!)', packLine+'\n  return check(goal,t,branchRoots[i]!)')
if (!replay.includes('if(process.env.LAB_LIVE_CUTS')) replay = swap(replay, '  return check(goal,t,branchRoots[i]!)', "  if(process.env.LAB_LIVE_CUTS==='1'){\n   const started=performance.now(),shared=shareLemmaCuts(goal,t,{path:branchRoots[i]!,until:wallAt()})\n   console.log(JSON.stringify({liveCuts:!!shared,totalMs:performance.now()-started,...shared?.stats}))\n   if(shared)return true\n  }\n  return check(goal,t,branchRoots[i]!)")
replay = swap(replay, ',trace,...(cores.length?', ",trace:process.env.LAB_PACK_SUMMARY==='1'?[]:trace,...(cores.length?")
writeFileSync(join(snapshot,'research/track-m/count-case-replay.ts'),replay)
const files = ['core/lemma-cuts.ts','kernel/kernel.ts','kernel/prove.ts','research/track-m/count-case-replay.ts','research/track-m/lemma-origin-dump.ts']
writeFileSync(join(input,'sharing-manifest.json'),JSON.stringify({sourceManifest:createHash('sha256').update(read(join(input,'manifest.json'))).digest('hex'),overlays:Object.fromEntries(files.map(f=>[f,createHash('sha256').update(read(join(snapshot,f))).digest('hex')]))},null,2)+'\n')
console.log(JSON.stringify({input, overlays:files}))
