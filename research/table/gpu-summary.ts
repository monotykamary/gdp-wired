// The GPU phase's tables: `bun research/table/gpu-summary.ts <gpu run dir> <cpu twin run dir>` (the same jobs, the
// first on Modal GPUs with --table-target/--target/--fp-target gpu, the second on CPU containers with cpu: Handwired's
// CPU loop runner running the same word programs).
import {readFileSync} from 'node:fs'

type Job = {name: string, code: number, seconds: number, out: string, gpu?: string}
const read = (d: string) => new Map(readFileSync(`${d}/results.jsonl`, 'utf8').split('\n').filter(Boolean).map(l => JSON.parse(l) as Job).map(j => [j.name, j]))
const result = (j?: Job): Record<string, any> | undefined => { if (!j) return undefined; for (const l of j.out.split('\n').reverse()) if (l.startsWith('{"stage":"result"')) { try { return JSON.parse(l) } catch { /* partial */ } } return undefined }
const [gdir, cdir] = process.argv.slice(2) as [string, string]
const G = read(gdir), C = read(cdir)
const median = (xs: number[]) => { if (!xs.length) return NaN; const s = [...xs].sort((a, b) => a - b); return s.length % 2 ? s[(s.length - 1) / 2]! : (s[s.length / 2 - 1]! + s[s.length / 2]!) / 2 }
const sum = (xs: number[]) => xs.reduce((a, b) => a + b, 0)
const isTip = (n: string) => n.endsWith('.smt2'), isTerm = (n: string) => n.endsWith('.ari') || n.startsWith('termination'), isChc = (n: string) => !isTip(n) && !isTerm(n)
const gpus = new Set([...G.values()].map(j => j.gpu).filter(Boolean))
console.log(`GPU: ${[...gpus].join('; ')}; jobs ${G.size} (GPU), ${C.size} (CPU twin); GPU container seconds ${sum([...G.values()].map(j => j.seconds)).toFixed(1)}, CPU ${sum([...C.values()].map(j => j.seconds)).toFixed(1)}`)

// CHC: the columns kernel (bounds + fingerprints) and the implications kernel, per predicate
{
  const gp = [...G.values()].filter(j => isChc(j.name)).map(j => result(j)?.gpu).filter(Boolean)
  const cp = [...C.values()].filter(j => isChc(j.name)).map(j => result(j)?.gpu).filter(Boolean)
  const preds = (xs: any[]) => xs.flatMap(x => x.preds as any[]).filter(p => p.fits && p.runMs !== undefined)
  const pg = preds(gp), pc = preds(cp)
  console.log(`\nCHC, ${gp.length} tasks on the GPU (${cp.length} on the CPU twin); predicates ${pg.length}; columns per predicate median ${median(pg.map(p => p.columns))}, max ${Math.max(...pg.map(p => p.columns))}; rows median ${median(pg.map(p => p.rows))}, max ${Math.max(...pg.map(p => p.rows))}`)
  console.log(`  device setup per task (ms): median ${median(gp.map(x => x.setupMs))}`)
  for (const [name, xs] of [['GPU', pg], ['CPU twin (Handwired loop runner)', pc]] as const) {
    console.log(`  ${name}: columns compile ms sum ${sum(xs.map(p => p.compileMs))}, run ms sum ${sum(xs.map(p => p.runMs))}; implies compile ${sum(xs.filter(p => p.impliesCompileMs !== undefined).map(p => p.impliesCompileMs))}, run ${sum(xs.filter(p => p.impliesRunMs !== undefined).map(p => p.impliesRunMs))}`)
  }
  console.log(`  plain JavaScript (typed arrays) columns ms sum ${sum(pg.map(p => p.jsMs))}; exact table.ts (BigInt) observe + bounds ms sum ${sum(pg.map(p => p.exactMs))}; exact Q4 ms sum ${sum(pg.map(p => p.exactQ4Ms))}; fingerprint groups' recheck ms sum ${sum(pg.map(p => p.recheckMs))}; implies JS ms sum ${sum(pg.filter(p => p.impliesJsMs !== undefined).map(p => p.impliesJsMs))}`)
  console.log(`  disagreements: GPU vs its JS twin ${sum(pg.map(p => p.twinDiff))} columns; GPU bounds vs exact ${sum(pg.map(p => p.exactDiff))} columns; fingerprint false merges ${sum(pg.map(p => p.falseMerges))} (groups ${sum(pg.map(p => p.fpGroups))}, exact groups ${sum(pg.map(p => p.exactGroups))}); implies vs JS ${sum(pg.filter(p => p.impliesTwinDiff !== undefined).map(p => p.impliesTwinDiff))} pairs; CPU twin vs JS ${sum(pc.map(p => p.twinDiff))} columns, ${sum(pc.filter(p => p.impliesTwinDiff !== undefined).map(p => p.impliesTwinDiff))} pairs`)
  console.log(`  predicates whose rows don't fit i32: ${gp.flatMap(x => (x.preds as any[]).filter(p => !p.fits)).length}`)
}

// Termination: the box sampler for the rules the runs never took
{
  const names = [...G.keys()].filter(isTerm)
  let rulesG = 0, pointsG = 0, runG = 0, compileG = 0, twinG = 0, diffDocs = 0, hits = 0, exactFalse = 0, skipped = 0, runC = 0, compileC = 0, rulesC = 0, sameAnswer = 0, both = 0, boxTasks = 0
  const ansG = new Map<string, number>(), ansC = new Map<string, number>(), setups: number[] = []
  for (const n of names) {
    const g = result(G.get(n)), c = result(C.get(n))
    if (g) { ansG.set(g.answer, (ansG.get(g.answer) ?? 0) + 1); setups.push(g.boxTarget?.setupMs ?? 0) }
    if (c) ansC.set(c.answer, (ansC.get(c.answer) ?? 0) + 1)
    if (g && c) { both++; if (g.answer === c.answer) sameAnswer++ }
    if (g?.box?.length) boxTasks++
    for (const s of (g?.box ?? []) as any[]) { if (s.skipped) { skipped++; continue } rulesG++; pointsG += s.points; runG += s.runMs; compileG += s.compileMs; twinG += s.twinMs ?? 0; diffDocs += s.twinDiffDocs ?? 0; hits += s.hits; exactFalse += s.exactFalse }
    for (const s of (c?.box ?? []) as any[]) { if (s.skipped) continue; rulesC++; runC += s.runMs; compileC += s.compileMs }
  }
  console.log(`\nTermination (${names.length} tasks, z3 runs then the box for the rules they never took): ${boxTasks} tasks used the box; rules boxed ${rulesG} (skipped ${skipped}), points ${pointsG}`)
  console.log(`  GPU: device setup median ${median(setups)} ms a task; compile ms sum ${compileG}, run ms sum ${runG}; its CPU twin in the same container: run ms sum ${twinG}; documents whose masks differ ${diffDocs}; points kept ${hits}, of which the exact evaluator refuses ${exactFalse}`)
  console.log(`  CPU twin on CPU containers: rules ${rulesC}, compile ms sum ${compileC}, run ms sum ${runC}`)
  console.log(`  answers: GPU ${JSON.stringify([...ansG])}, CPU twin ${JSON.stringify([...ansC])}; the same on ${sameAnswer} of ${both}`)
  const wg = names.map(n => G.get(n)?.seconds ?? NaN).filter(x => !isNaN(x)), wc = names.map(n => C.get(n)?.seconds ?? NaN).filter(x => !isNaN(x))
  console.log(`  wall per task (s): GPU median ${median(wg)}, sum ${sum(wg).toFixed(1)}; CPU median ${median(wc)}, sum ${sum(wc).toFixed(1)}`)
}

// TIP: Q4's fingerprints of the last size's columns
{
  const rows = [...G.keys()].filter(isTip).map(n => ({n, g: result(G.get(n))?.fp, c: result(C.get(n))?.fp, r: result(G.get(n))}))
  const ok = rows.filter(x => x.g)
  console.log(`\nTIP (${rows.length} problems; ${ok.length} with a GPU fingerprint pass): columns per problem median ${median(ok.map(x => x.g.columns))}, max ${Math.max(...ok.map(x => x.g.columns))}`)
  console.log(`  CPU (the values' text as the key) ms sum ${sum(ok.map(x => x.g.cpuMs))}; GPU: intern ${sum(ok.map(x => x.g.internMs))} + compile ${sum(ok.map(x => x.g.compileMs))} + run ${sum(ok.map(x => x.g.runMs))} + group and recheck ${sum(ok.map(x => x.g.groupAndRecheckMs))} ms; CPU twin run ${sum(rows.filter(x => x.c).map(x => x.c.runMs))} ms`)
  console.log(`  partitions agree with the CPU's: ${ok.filter(x => x.g.partitionsAgree).length} of ${ok.length}; false merges ${sum(ok.map(x => x.g.falseMerges))}`)
  console.log(`  during enumeration: evaluation ms sum ${sum(ok.map(x => x.r!.evalMs))}, fingerprints (text) ms sum ${sum(ok.map(x => x.r!.fpMs))}`)
}
