// The bar: a candidate against a base on every benchmark, in one command, and one report.
//
//   bun gates/bar.ts [--cand <rev | dir>] [--base <rev>] [--only chc,its,...] [--quick] [--together]
//                    [--runs 3] [--reruns 3] [--backend modal|boat|auto] [--rivals] [--budget <$>] [--name <out>]
//   bun gates/bar.ts baseline --base <rev> [--runs 3] [--only ...]     the shared baseline alone
//   bun gates/bar.ts devset [--from <base key>] [--write]             the quick mode's dev sets from a baseline
//   bun gates/bar.ts read <view> <run dir>...                         a run directory's headline, as the bar reads it
//
// Groups (`--only`): chc, its (the task's statement and per component), sv (both), tip (`--rivals`: cvc5 and Vampire
// too), f1 and f2 (the frontier corpora), rw (the real-world corpus), g332 (research/dag's step goals), suite and
// suite-usual (modal/suite.json, by default and --usual, one mode after the other), onecpu (the 5 s-limited tests on
// 1 vCPU, ten jobs a side), lean (a sample of the ITS run's recurrent sets checked by Lean: 48 in full mode, 6 in quick).
//
// The candidate is a commit (a worktree is made for it under <main>/runs/bar/trees/) or a directory, run as it is
// (default: this checkout). The base (default: main) comes from the shared baseline, <main>/runs/bar/base/<sha>-<backend>-r<v>/:
// N full runs of it (--runs, 3), made once and reused by every candidate; `--together` launches the base beside the
// candidate instead. Tasks whose first-pass verdict differs from the base's (its majority over its runs) are run
// --reruns times more on each side, together. onecpu and g332 time the two sides, so their base always runs beside
// the candidate. `--quick` runs each benchmark's dev set (gates/bar-dev.json: stratified by family and by how main
// did) and predicts the full delta from it. Every launch is a runner's own command in its side's tree (python3
// compare/chc/modal_chc.py ..., python3 modal/run.py ...), so a figure here is that runner's.
//
// Cost hygiene: the runners' functions have scaledown_window=2 and their own timeouts; each launch here has a wall
// cap and is stopped (SIGINT, then SIGTERM, then SIGKILL, by its exact pid) at it; on any exit the bar stops every
// launch it started and runs modal/reap.sh in every tree it used. Each tree's first launch of a group is a pilot of
// one or two tasks, read before the fan-out. `--budget` (default $25 full, $6 quick) is checked against the real spend
// of the bar's own apps (`modal billing report`) between phases and every five minutes.
import {closeSync, cpSync, existsSync, mkdirSync, openSync, readFileSync, readdirSync, realpathSync, rmSync, statSync, symlinkSync, writeFileSync} from 'node:fs'
import {dirname, join, resolve} from 'node:path'
import {type Dev, type Obs, type Rows, type TaskCmp, VIEWS, compareTasks, differing, goalSig, goals, hash, inBand, keyOfCmd, predict, testTimes, devSet} from './bar-lib.ts'

const VERSION = 1
const argv = process.argv.slice(2)
const sub = argv[0] && !argv[0].startsWith('--') ? argv.shift()! : 'run'
const opt = (k: string, d = '') => { const i = argv.indexOf(`--${k}`); return i < 0 ? d : argv[i + 1] ?? d }
const flag = (k: string) => argv.includes(`--${k}`)
// --smoke: the bar itself end to end on each group's pilot tasks, the base launched together (nothing cached)
const smoke = flag('smoke'), quick = flag('quick'), together = flag('together') || smoke, rivals = flag('rivals'), backend = opt('backend', 'modal')
const nRuns = Number(opt('runs', '3')), nReruns = Number(opt('reruns', '3')), maxProcs = Number(opt('procs', '24'))
const budget = Number(opt('budget', quick ? '6' : '25'))
if (!['modal', 'boat', 'auto'].includes(backend)) throw new Error('--backend modal | boat | auto')

// ------------------------------------------------------------------------------------------------------- the shell
const out0 = (args: string[], cwd?: string) => {
  const p = Bun.spawnSync(args, {cwd, stdout: 'pipe', stderr: 'pipe'})
  if (p.exitCode !== 0) throw new Error(`${args.join(' ')}: ${p.stderr.toString().slice(-600)}`)
  return p.stdout.toString().trim()
}
const HERE = dirname(import.meta.path)
const MAIN = dirname(out0(['git', 'rev-parse', '--path-format=absolute', '--git-common-dir'], HERE))
const BAR = process.env.GDPW_BAR_DIR ?? join(MAIN, 'runs', 'bar')
const log = (...a: unknown[]) => console.log(`[bar ${new Date().toISOString().slice(11, 19)}]`, ...a)
const mkdir = (d: string) => mkdirSync(d, {recursive: true})
const readJson = <T>(f: string): T => JSON.parse(readFileSync(f, 'utf8')) as T
const writeJson = (f: string, x: unknown) => { mkdir(dirname(f)); writeFileSync(f, JSON.stringify(x, null, 1) + '\n') }

let stopping = false
type Child = {pid: number, kill: (s: NodeJS.Signals) => void, what: string, cwd: string}
const live = new Map<number, Child>()
const treesUsed = new Set<string>()
let slots = maxProcs
const waiting: (() => void)[] = []
const acquire = async () => { while (slots <= 0) await new Promise<void>(r => waiting.push(r)); slots-- }
const release = () => { slots++; waiting.shift()?.() }

// One launch: argv (no shell, so the pid is the runner's own), its output to a log, stopped at its wall cap.
async function run(args: string[], o: {cwd: string, log: string, stdout?: string, env?: Record<string, string>, cap: number}): Promise<number> {
  await acquire()
  if (stopping) { release(); return 130 }  // nothing new once the bar is stopping
  mkdir(dirname(o.log))
  const fd = openSync(o.log, 'a'), sfd = o.stdout ? openSync(o.stdout, 'w') : fd
  treesUsed.add(o.cwd)
  try {
    const p = Bun.spawn(args, {cwd: o.cwd, stdout: sfd, stderr: fd, env: {...process.env, ...o.env}})
    const c: Child = {pid: p.pid, kill: s => p.kill(s), what: args.slice(0, 3).join(' '), cwd: o.cwd}
    live.set(p.pid, c)
    const timer = setTimeout(() => { log(`cap of ${o.cap} s reached: stopping ${c.what} (pid ${c.pid})`); void stop(c) }, o.cap * 1000)
    const code = await p.exited
    clearTimeout(timer)
    live.delete(p.pid)
    return code
  } finally {
    closeSync(fd)
    if (o.stdout) closeSync(sfd)
    release()
  }
}
// SIGINT is the runners' Ctrl-C (every call they spawned cancelled), SIGTERM their other path to it, SIGKILL last.
async function stop(c: Child) {
  for (const [s, wait] of [['SIGINT', 45], ['SIGTERM', 45], ['SIGKILL', 5]] as const) {
    if (!live.has(c.pid)) return
    try { c.kill(s) } catch { return }
    for (let i = 0; i < wait && live.has(c.pid); i++) await Bun.sleep(1000)
  }
}
async function stopAll(why: string) {
  if (stopping) return
  stopping = true
  log(`stopping ${live.size} launch(es): ${why}`)
  await Promise.all([...live.values()].map(stop))
  reap()
}
function reap() {
  for (const t of new Set([...treesUsed, HERE + '/..'])) {
    if (!existsSync(join(t, 'modal', 'reap.sh'))) continue
    const p = Bun.spawnSync(['sh', join(t, 'modal', 'reap.sh')], {cwd: t, stdout: 'pipe', stderr: 'pipe'})
    const said = p.stdout.toString().split('\n').filter(l => l.startsWith('stopped orphan')).join('; ')
    if (said) log(`reap ${t}: ${said}`)
  }
}
for (const s of ['SIGINT', 'SIGTERM', 'SIGHUP'] as const) process.on(s, () => { void stopAll(s).then(() => process.exit(130)) })
process.on('exit', () => { for (const c of live.values()) try { c.kill('SIGINT') } catch { /* gone */ } })

// ------------------------------------------------------------------------------------------------------- the trees
type Tree = {path: string, sha: string, key: string, clean: boolean, label: string}
// A directory with no uncommitted changes is its commit's tree; one with changes is copied (what git sees, untracked
// files too, without node_modules, runs/ and .git) to <bar>/trees/<sha>+<hash of the changes>, so editing it while
// the runners upload it changes nothing, and the same changes are the same tree.
function treeOf(rev: string): Tree {
  if (existsSync(rev) && statSync(rev).isDirectory()) {
    const src = realpathSync(rev), sha = out0(['git', 'rev-parse', 'HEAD'], src)
    const dirt = out0(['git', 'status', '--porcelain', '--untracked-files=all'], src)
    if (!dirt) return {...treeOf(sha), label: `${src} at ${sha.slice(0, 12)}`}
    const h = new Bun.CryptoHasher('sha256')
    h.update(dirt + out0(['git', 'diff', 'HEAD'], src))
    for (const f of out0(['git', 'ls-files', '-o', '--exclude-standard'], src).split('\n').filter(Boolean)) h.update(f + '\0' + (existsSync(join(src, f)) ? readFileSync(join(src, f)).toString('base64') : ''))
    const key = `${sha.slice(0, 12)}+${h.digest('hex').slice(0, 8)}`, path = join(BAR, 'trees', key)
    if (!existsSync(join(path, '.bar-ready'))) {
      log(`copying ${src} (uncommitted changes) to ${path}`)
      mkdir(path)
      out0(['rsync', '-a', '--delete', '--exclude', 'node_modules/', '--exclude', '/runs/', '--exclude', '.git', '--exclude', '*.olean', '--exclude', '*.ilean', '--exclude', '.lake/', '--exclude', 'modal/.live/', '--exclude', '.bar-lean/', `${src}/`, `${path}/`])
      out0(['bun', 'install', '--frozen-lockfile'], path)
      writeFileSync(join(path, '.bar-ready'), key + '\n')
    }
    return {path, sha, clean: false, key, label: `${src} (uncommitted changes, copied as ${key})`}
  }
  const sha = out0(['git', 'rev-parse', '--verify', `${rev}^{commit}`], MAIN)
  const path = join(BAR, 'trees', sha.slice(0, 12))
  mkdir(join(BAR, 'trees'))
  // research/query reads the main checkout's dumped goals as <tree>/../gdp-wired (its MAIN)
  if (!existsSync(join(BAR, 'trees', 'gdp-wired'))) symlinkSync(MAIN, join(BAR, 'trees', 'gdp-wired'))
  if (!existsSync(join(path, '.bar-ready'))) {
    log(`making the tree of ${sha.slice(0, 12)} at ${path}`)
    if (!existsSync(path)) out0(['git', 'worktree', 'add', '--detach', path, sha], MAIN)
    out0(['git', 'submodule', 'update', '--init'], path)
    out0(['bun', 'install', '--frozen-lockfile'], path)
    writeFileSync(join(path, '.bar-ready'), sha + '\n')
  }
  return {path, sha, clean: true, key: sha.slice(0, 12), label: `${rev} (${sha.slice(0, 12)})`}
}

// -------------------------------------------------------------------------------------------------------- the groups
type Side = 'cand' | 'base'
type Pass = {group: string, side: Side, tree: Tree, dir: string, tasks?: string[], quickSize?: boolean, backend?: string}
type Job = {name: string, cmd: string, cwd?: string, cpu?: number, memory?: number, timeout?: number}
type Group = {key: string, views: string[], cap: number, launch: (p: Pass) => Promise<number>, pairAlways?: boolean, noRerun?: boolean, candOnly?: boolean, after?: string, inQuick: boolean}

const py = (p: Pass, script: string, args: string[], cap: number) => run(['python3', script, '--backend', p.backend ?? backend, '--out', p.dir, ...args], {cwd: p.tree.path, log: `${p.dir}.log`, cap})
const listFile = (p: Pass, sep: string) => { const f = `${p.dir}.tasks`; writeFileSync(f, p.tasks!.join(sep)); return f }
async function jobsPass(p: Pass, jobs: Job[], keyOf: (j: Job) => string, cap: number, extra: string[] = []) {
  const keep = p.tasks ? new Set(p.tasks) : undefined, js = keep ? jobs.filter(j => keep.has(keyOf(j))) : jobs
  writeJson(`${p.dir}.jobs.json`, js)
  writeJson(`${p.dir}.keys.json`, Object.fromEntries(js.map(j => [j.name, keyOf(j)])))
  if (!js.length) { mkdir(p.dir); return 0 }
  return run(['python3', 'modal/run.py', '--backend', p.backend ?? backend, '--jobs', `${p.dir}.jobs.json`, '--out', p.dir, ...extra], {cwd: p.tree.path, log: `${p.dir}.log`, cap})
}
async function jobsOf(p: Pass, args: string[]): Promise<Job[]> {
  const f = `${p.dir}.all-jobs.json`
  mkdir(dirname(f))
  const code = await run(args, {cwd: p.tree.path, log: `${p.dir}.log`, stdout: f, cap: 300})
  if (code !== 0) throw new Error(`${args.join(' ')} exit ${code}`)
  return readJson<Job[]>(f)
}
const corpusPass = (corpus: string) => async (p: Pass) => {
  const jobs = await jobsOf(p, ['bun', `research/${corpus}/jobs.ts`])
  mkdir(p.dir)
  // the broken variants, which count when refused (research/<corpus>/score.ts's tally)
  await run(['bun', '-e', `const {corpus} = await import('./research/${corpus}/corpus.ts'); console.log(JSON.stringify(corpus.filter(i => i.broken).map(i => i.id)))`],
    {cwd: p.tree.path, log: `${p.dir}.log`, stdout: `${p.dir}/broken.json`, cap: 300})
  return jobsPass(p, jobs, j => keyOfCmd(j.cmd) ?? j.name, 1800)
}
const GROUPS: Group[] = [
  {key: 'chc', views: ['chc'], cap: 2400, inQuick: true, launch: p => py(p, 'compare/chc/modal_chc.py', ['--tools', 'gdp', ...(p.tasks ? ['--tasks-json', listJson(p)] : [])], 2400)},
  {key: 'its', views: ['its', 'its-scc'], cap: 2400, inQuick: true, launch: p => py(p, 'compare/term/modal_term.py', ['--tools', 'gdp,gdp-scc', ...(p.tasks ? ['--tasks-file', listFile(p, '\n')] : [])], 2400)},
  {key: 'sv', views: ['sv', 'sv-scc'], cap: 1800, inQuick: true, launch: p => py(p, 'compare/term/modal_sv.py', ['--tools', 'gdp,gdp-scc', ...(p.tasks ? ['--only', p.tasks.join('|')] : [])], 1800)},
  {key: 'tip', views: rivals ? ['tip', 'tip-cvc5', 'tip-cvc5cg', 'tip-vampire'] : ['tip'], cap: 1800, inQuick: true,
    launch: p => py(p, 'compare/tip/modal_tip.py', ['--tools', rivals && p.side === 'cand' && !p.tasks ? 'gdp,cvc5,cvc5cg,vampire' : 'gdp', ...(p.tasks ? ['--only', p.tasks.join('|')] : [])], 1800)},
  {key: 'f1', views: ['f1'], cap: 1800, inQuick: true, launch: corpusPass('frontier')},
  {key: 'f2', views: ['f2'], cap: 1800, inQuick: true, launch: corpusPass('frontier2')},
  {key: 'rw', views: ['rw'], cap: 1800, inQuick: true, launch: async p => jobsPass(p, await jobsOf(p, ['bun', 'research/realworld/jobs.ts']), j => keyOfCmd(j.cmd) ?? j.name, 1800)},
  // research/query's runner is Modal's (`modal run`) whatever --backend says; GDP_QUERY_BASE pointed at nothing, so
  // no second tree is mounted
  {key: 'g332', views: ['g332'], cap: 1200, inQuick: true, pairAlways: true, noRerun: true, launch: async p => {
    const jobs = (await jobsOf(p, ['python3', 'research/query/jobs.py', 'g332'])).filter(j => !p.tasks || p.tasks.includes(j.name))
    writeJson(`${p.dir}.jobs.json`, jobs)
    return run(['modal', 'run', 'research/query/modal_query.py', '--jobs', `${p.dir}.jobs.json`, '--out', p.dir], {cwd: p.tree.path, log: `${p.dir}.log`, env: {GDP_QUERY_BASE: join(BAR, 'none')}, cap: 1200})
  }},
  {key: 'suite', views: ['suite'], cap: 2400, inQuick: false, launch: p => jobsPass(p, readJson<Job[]>(join(p.tree.path, 'modal/suite.json')), j => j.name, 2400)},
  {key: 'suite-usual', views: ['suite-usual'], cap: 2400, inQuick: false, after: 'suite', launch: p => jobsPass(p, readJson<Job[]>(join(p.tree.path, 'modal/suite.json')), j => j.name, 2400, ['--usual'])},
  {key: 'onecpu', views: [], cap: 1500, inQuick: true, pairAlways: true, noRerun: true, launch: p => {
    const n = smoke ? 1 : p.quickSize ? 3 : 10, jobs: Job[] = []
    for (let i = 0; i < n; i++) for (const t of ['data', 'infer']) jobs.push({name: `${p.side}-${t}-${i}`, cmd: `bun install --frozen-lockfile >/dev/null 2>&1; bun test core/${t}.test.ts 2>&1`, cpu: 1.0, timeout: 600})
    return jobsPass(p, jobs, j => j.name, 1500)
  }},
  {key: 'lean', views: ['lean'], cap: 3600, inQuick: true, candOnly: true, noRerun: true, after: 'its', launch: leanPass},
]
function listJson(p: Pass) { const f = `${p.dir}.tasks.json`; writeJson(f, p.tasks); return f }

// The Lean sample: nonterminating answers by a recurrent set in the candidate's ITS run, each a theorem `NeverEnds
// <task>_loop` by compare/term/recur-lean.ts and Lean 4.34.0 (the 0.28.0 release's: the gained ones first, the s1
// family, the sets closed by cases, then drawn by the commit; 48, or 6 in quick mode).
const leanInputs = new Map<string, {rows: {task: string, stages: {by?: string, recur?: object}[]}[], gained: Set<string>}>()
async function leanPass(p: Pass): Promise<number> {
  const inp = leanInputs.get(p.side)
  if (!inp) { mkdir(p.dir); return 0 }
  const term = readFileSync(join(p.tree.path, 'compare/term/modal_term.py'), 'utf8'), ari = /ARI_COMMIT = "(\w+)"/.exec(term)?.[1]
  if (!ari) throw new Error('no ARI_COMMIT in compare/term/modal_term.py')
  const bench = join(BAR, 'bench', `tpdb-${ari}`)
  if (!existsSync(join(bench, '.done'))) {
    mkdir(bench)
    const code = await run(['bash', '-c', `curl -fsSL https://codeload.github.com/TermCOMP/TPDB-ARI/tar.gz/${ari} | tar xz -C '${bench}' --strip-components 1 TPDB-ARI-${ari}/Integer_Transition_Systems`], {cwd: bench, log: `${p.dir}.log`, cap: 600})
    if (code !== 0) throw new Error('TPDB-ARI download failed')
    writeFileSync(join(bench, '.done'), ari)
  }
  const n = smoke ? 1 : p.quickSize ? 6 : 48, rows = inp.rows.filter(r => r.stages.at(-1)?.by === 'recurrent set' && r.stages.at(-1)?.recur)
  const rank = (r: {task: string, stages: {recur?: object}[]}) => [inp.gained.has(r.task) ? 0 : 1, /\/s1[.-]/.test(r.task) ? 0 : 1, 'cases' in (r.stages.at(-1)!.recur!) ? 0 : 1, hash(p.tree.sha + r.task)]
  const byRank = (a: number[], b: number[]) => { for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return a[i]! - b[i]!; return 0 }
  const pick = [...rows].sort((a, b) => byRank(rank(a), rank(b))).slice(0, n)
  const id = `.bar-lean/${p.dir.split('/').slice(-3).join('-')}`, here = join(p.tree.path, id)
  rmSync(here, {recursive: true, force: true})
  mkdir(here)
  const pre = 'export LEAN_PATH=$PWD:$(dirname $(dirname $(readlink -f $(elan which lean))))/lib/lean; for f in Cert Kernel Progress StepLaw Steps Sets Live NonTerm; do { [ -f $f.olean ] || lean -o $f.olean $f.lean; } > /dev/null 2>&1 || { echo build-failed $f; exit 1; }; done; '
  const jobs: Job[] = pick.map((r, k) => {
    writeFileSync(join(here, `${k}.jsonl`), JSON.stringify(r) + '\n')
    mkdir(dirname(join(here, 'bench', r.task)))
    cpSync(join(bench, r.task), join(here, 'bench', r.task))
    const q = `'${r.task.replace(/'/g, `'\\''`)}'`
    return {name: `lean-${k}`, cwd: 'lean-kernel', cpu: 4.0, memory: 16384, timeout: 2100,
      cmd: `${pre}echo ${q}; (cd .. && bun install --frozen-lockfile > /dev/null 2>&1; time bun compare/term/recur-lean.ts ${id}/${k}.jsonl ${id}/bench /tmp/its.lean) && ls -la /tmp/its.lean && (time timeout -s KILL 1800 lean /tmp/its.lean) > lean.out 2>&1; s=$?; tail -8 lean.out; grep -c '^theorem' /tmp/its.lean; echo lean-exit $s; exit $s`}
  })
  try { return await jobsPass(p, jobs, j => j.name, 3600) } finally { rmSync(here, {recursive: true, force: true}) }
}

// ------------------------------------------------------------------------------------------------------ the dev set
const DEV_FILE = join(HERE, 'bar-dev.json')
// A group's pilot when the dev file names none: the fastest solved tasks of main's runs (runs/chc7/, main a269124).
const PILOT: Record<string, string[]> = {
  chc: ['hcai-bench/svcomp/O3/O3_terminator_01_false-unreach-call_true-termination_000.yml', 'eldarica-misc/LIA/llreve/nested-while_unsafe.c-1_000.yml'],
  its: ['Integer_Transition_Systems/From_AProVE_2014/Continue.jar-obl-8.ari', 'Integer_Transition_Systems/From_AProVE_2014/Velroyen08-fib.jar-obl-8.ari'],
  sv: ['termination-restricted-15/Ex05.yml', 'termination-restricted-15/Ex07.yml'], tip: ['tip2015/nat_boring_max_min_abs.smt2', 'tip2015/nat_lt_ne.smt2'],
  f1: ['nonlinear/cauchy-schwarz', 'nonlinear/cubes'], f2: ['term/Continue1.jar-obl-8', 'chc/H/durationThm_1_e1_197'],
  rw: ['feature flag/growthbook/forceRuleRollout#6', 'feature flag/growthbook/forceRuleRollout#4'], g332: ['g332__eldarica-misc__LIA__HOLA__06.c_000'],
  suite: ['run-proofs'], 'suite-usual': ['run-proofs'],
}
type DevFile = {made: string, views: Record<string, Dev>, pilot: Record<string, string[]>}
const devFile = (): DevFile | undefined => existsSync(DEV_FILE) ? readJson<DevFile>(DEV_FILE) : undefined
const groupDev = (g: Group): string[] | undefined => {
  const d = devFile()
  if (!d) throw new Error(`--quick needs ${DEV_FILE} (bun gates/bar.ts devset --write)`)
  const ts = g.views.flatMap(v => Object.keys(d.views[v]?.tasks ?? {}))
  return ts.length ? [...new Set(ts)].sort() : undefined
}

// -------------------------------------------------------------------------------------------------- the passes run
const views = (g: Group) => g.views.map(v => VIEWS[v]!)
const parse = (g: Group, dir: string, tree: Tree) => new Map(views(g).map(v => [v.key, v.parse(dir, tree.path)]))
type Meta = {group: string, side: Side, tree: string, sha: string, backend: string, started: string, wall_s: number, code: number, apps: string[], tasks: number | 'all', where?: unknown, retried?: string[]}
const appsIn = (f: string) => existsSync(f) ? [...new Set(readFileSync(f, 'utf8').match(/\bap-[A-Za-z0-9]{20,}\b/g) ?? [])] : []

async function pass(g: Group, p: Pass): Promise<Meta> {
  const t0 = Date.now(), started = new Date().toISOString()
  mkdir(dirname(p.dir))
  if (p.tasks) writeJson(`${p.dir}.given.json`, p.tasks)
  let code: number
  try { code = await g.launch(p) } catch (e) { writeFileSync(`${p.dir}.log`, `\n${String(e)}\n`, {flag: 'a'}); code = -1 }
  // A task the backend failed (a VM or container lost, a mount error, a call that raised, a row or a job missing) is
  // not the prover's answer: it runs once more on Modal and its row replaces the failed one.
  const failed = code === 130 || stopping ? [] : backendFailed(p.dir)
  let retried: string[] | undefined
  if (failed.length && failed.length <= 400) {
    log(`${g.key} ${p.side} ${p.dir.split('/').at(-1)}: ${failed.length} task(s) failed on the backend; once more on Modal`)
    const r: Pass = {...p, dir: `${p.dir}-retry`, tasks: failed, backend: 'modal'}
    try { await g.launch(r) } catch (e) { writeFileSync(`${r.dir}.log`, `\n${String(e)}\n`, {flag: 'a'}) }
    mergeRetry(p.dir, r.dir)
    retried = failed
  }
  const where = existsSync(join(p.dir, 'backends.json')) ? readJson<{where?: unknown}>(join(p.dir, 'backends.json')).where : undefined
  const m: Meta = {group: g.key, side: p.side, tree: p.tree.label, sha: p.tree.sha, backend, started, wall_s: Math.round((Date.now() - t0) / 100) / 10, code, apps: appsIn(`${p.dir}.log`), tasks: p.tasks?.length ?? 'all', where, retried}
  if (retried) m.apps.push(...appsIn(`${p.dir}-retry.log`))
  writeJson(`${p.dir}.meta.json`, m)
  log(`${g.key} ${p.side} ${p.dir.split('/').at(-1)}: exit ${code}, ${m.wall_s} s${m.apps.length ? `, ${m.apps.join(' ')}` : ''}`)
  return m
}

const INFRA = /\bmount(ed|ing)?\b|\bboat\b|\bVM\b|preempt|never ran|ConflictError|ExecutionError|ConnectionError|RemoteError|InternalFailure|FunctionTimeoutError|InputCancellation|Container .*(terminated|died|lost)|lost under/i
function backendFailed(dir: string): string[] {
  const out = new Set<string>()
  if (existsSync(join(dir, 'results.jsonl'))) {
    // a compare runner: its tasks (all, or those it was given) against its rows
    const rows = readFileSync(join(dir, 'results.jsonl'), 'utf8').split('\n').filter(Boolean).flatMap(l => { try { return [JSON.parse(l) as {tool: string, task: string, answer: string, err?: string}] } catch { return [] } })
    const given = existsSync(`${dir}.given.json`) ? readJson<string[]>(`${dir}.given.json`) : undefined
    const all = given ?? (existsSync(join(dir, 'tasks.json')) ? ((t: unknown) => (Array.isArray(t) ? t as {task: string}[] : (t as {tasks: string[]}).tasks.map(task => ({task}))).map(x => x.task))(readJson<unknown>(join(dir, 'tasks.json'))) : [])
    const tools = [...new Set(rows.map(r => r.tool).filter(t => t !== '?'))]
    for (const r of rows) if (r.tool !== '?' && r.answer === 'error' && INFRA.test(r.err ?? '')) out.add(r.task)
    for (const tool of tools) { const has = new Set(rows.filter(r => r.tool === tool).map(r => r.task)); for (const t of all) if (!has.has(t)) out.add(t) }
    if (!tools.length && rows.some(r => r.tool === '?')) for (const t of all) out.add(t)
  } else if (existsSync(`${dir}.keys.json`)) {
    // a job list: a job with no row, exit -1 (never ran, or its container died), or a log that says the backend failed
    const keys = readJson<Record<string, string>>(`${dir}.keys.json`), rows = summaryRowsOf(dir)
    for (const [job, key] of Object.entries(keys)) {
      const r = rows.get(job), logf = join(dir, `${job}.log`)
      if (!r || r.code === '-1' || (r.code !== '0' && existsSync(logf) && INFRA.test(readFileSync(logf, 'utf8').split('--- stderr ---')[1] ?? ''))) out.add(key)
    }
  }
  return [...out]
}
const summaryRowsOf = (dir: string) => new Map((existsSync(join(dir, 'summary.tsv')) ? readFileSync(join(dir, 'summary.tsv'), 'utf8').split('\n').filter(Boolean) : []).map(l => { const [n, code, secs, where] = l.split('\t'); return [n!, {code: code!, line: l, secs, where}] }))
function mergeRetry(dir: string, retry: string) {
  if (!existsSync(retry)) return
  if (existsSync(join(retry, 'results.jsonl'))) { writeFileSync(join(dir, 'results.jsonl'), readFileSync(join(retry, 'results.jsonl'), 'utf8'), {flag: 'a'}); return }
  const rows = summaryRowsOf(dir), again = summaryRowsOf(retry)
  mkdir(dir)
  for (const [n, r] of again) { rows.set(n, r); if (existsSync(join(retry, `${n}.log`))) cpSync(join(retry, `${n}.log`), join(dir, `${n}.log`)) }
  writeFileSync(join(dir, 'summary.tsv'), [...rows.values()].map(r => r.line + '\n').join(''))
}

// The pilot: one or two tasks of the group in this tree, end to end, read before its fan-out (once per tree).
async function pilot(g: Group, tree: Tree, side: Side, outDir: string): Promise<string | undefined> {
  if (g.noRerun || g.candOnly || smoke) return undefined
  const ok = join(BAR, 'pilots', `${tree.key}-${backend}-${g.key}-r${VERSION}.ok`)
  if (existsSync(ok)) return undefined
  const tasks = devFile()?.pilot[g.key] ?? PILOT[g.key]
  const p: Pass = {group: g.key, side, tree, dir: join(outDir, g.key, `pilot-${side}`), tasks}
  const m = await pass(g, p)
  const rows = [...parse(g, p.dir, tree).values()][0] ?? new Map()
  const good = [...rows.values()].filter(o => o.answer !== 'error' && o.answer !== 'missing' && !o.answer.startsWith('exit -'))
  if (m.code !== 0 && !rows.size) return `the pilot exited ${m.code} with no rows (${p.dir}.log)`
  if (!good.length) return `the pilot's ${rows.size} rows are all errors (${p.dir})`
  writeJson(ok, {at: new Date().toISOString(), dir: p.dir, rows: [...rows].map(([t, o]) => `${t}: ${o.answer} ${o.secs}`)})
  return undefined
}

// The shared baseline: N full runs of the base per group, under a lock, each kept once it ends (`.done`).
const cacheDir = (tree: Tree) => join(BAR, 'base', `${tree.key}-${backend}-r${VERSION}`)
async function baseline(g: Group, tree: Tree, n: number, outDir: string): Promise<string[]> {
  if (!tree.clean) throw new Error(`the base ${tree.label} has uncommitted changes: use --together`)
  const gdir = join(cacheDir(tree), g.key), lock = join(gdir, '.lock')
  const done = () => Array.from({length: n}, (_, i) => join(gdir, `run${i + 1}`)).filter(d => existsSync(`${d}/.done`))
  mkdir(gdir)
  let waited = false
  for (;;) {
    if (done().length >= n) return done()
    try {
      mkdirSync(lock)
      writeFileSync(join(lock, 'pid'), String(process.pid))
      break
    } catch {
      const pid = Number(existsSync(join(lock, 'pid')) ? readFileSync(join(lock, 'pid'), 'utf8') : 0)
      let alive = false
      try { process.kill(pid, 0); alive = pid > 0 } catch { alive = false }
      if (!alive) { rmSync(lock, {recursive: true, force: true}); continue }
      if (!waited) log(`${g.key}: the baseline is being made by pid ${pid}; waiting`)
      waited = true
      await Bun.sleep(20_000)
    }
  }
  try {
    const why = await pilot(g, tree, 'base', outDir)
    if (why) throw new Error(`${g.key} base pilot: ${why}`)
    const missing = Array.from({length: n}, (_, i) => join(gdir, `run${i + 1}`)).filter(d => !existsSync(`${d}/.done`))
    // one run after the other, so the runs see the machines at different times and their band holds that noise too
    log(`${g.key}: making ${missing.length} baseline run(s) of ${tree.label}, one after the other`)
    for (const d of missing) {
      if (stopping) break
      rmSync(d, {recursive: true, force: true})
      const m = await pass(g, {group: g.key, side: 'base', tree, dir: d})
      if (m.code === 0 && [...parse(g, d, tree).values()].some(r => r.size)) writeJson(`${d}/.done`, m)
      else log(`${g.key}: the baseline run ${d} exited ${m.code}: not kept`)
    }
    return done()
  } finally { rmSync(lock, {recursive: true, force: true}) }
}

type Result = {group: string, cand?: string, base: string[], reruns: {cand: string[], base: string[]}, differing: string[], quick?: string[], error?: string, metas: Meta[]}
// Each group's first pass, a side at a time and both, as gates the groups that follow one wait on (suite-usual after
// suite, side by side; lean after both of ITS's first passes).
type Gate = {p: Promise<unknown>, open: (x?: unknown) => void}
const gates = new Map<string, Gate>()
const gate = (k: string): Gate => {
  if (!gates.has(k)) { let open: (x?: unknown) => void = () => {}; const p = new Promise<unknown>(r => { open = r }); gates.set(k, {p, open}) }
  return gates.get(k)!
}
async function groupFlow(g: Group, cand: Tree, base: Tree, outDir: string, guard: () => boolean, inRun: Set<string>): Promise<Result> {
  const res: Result = {group: g.key, base: [], reruns: {cand: [], base: []}, differing: [], metas: []}
  const tasks = g.key === 'onecpu' || g.key === 'lean' ? undefined : smoke ? devFile()?.pilot[g.key] ?? PILOT[g.key] : quick ? groupDev(g) : undefined
  res.quick = tasks
  const gd = join(outDir, g.key)
  const after = g.after && inRun.has(g.after) ? g.after : undefined
  const sidePass = async (side: Side, tree: Tree): Promise<string> => {
    if (after) await gate(`${after}/${side}`).p
    if (g.key === 'lean') {
      const its = await gate('its/both').p as Result | undefined
      if (!its?.cand) throw new Error('no ITS run to sample')
      leanInputs.set(side, {rows: readFileSync(join(its.cand, 'results.jsonl'), 'utf8').split('\n').filter(Boolean).map(l => JSON.parse(l) as {tool: string, task: string, answer: string, stages: []}).filter(r => r.tool === 'gdp' && r.answer === 'nonterminating'),
        gained: new Set(its.base.length ? differing(VIEWS.its!.parse(its.cand, cand.path), its.base.map(b => VIEWS.its!.parse(b, base.path))) : [])})
    }
    const why = await pilot(g, tree, side, outDir)
    if (why) throw new Error(`${side} pilot: ${why}`)
    const p: Pass = {group: g.key, side, tree, dir: join(gd, `${side}-1`), tasks, quickSize: quick}
    res.metas.push(await pass(g, p))
    return p.dir
  }
  try {
    const basePromise: Promise<string[]> = g.candOnly ? Promise.resolve([]) : together || g.pairAlways ? sidePass('base', base).then(d => [d])
      : (after ? gate(`${after}/base`).p : Promise.resolve()).then(() => baseline(g, base, nRuns, outDir))
    void basePromise.then(() => gate(`${g.key}/base`).open(), () => gate(`${g.key}/base`).open())
    const candPromise = sidePass('cand', cand)
    void candPromise.then(() => gate(`${g.key}/cand`).open(), () => gate(`${g.key}/cand`).open())
    const [c, b] = await Promise.allSettled([candPromise, basePromise])
    if (c.status === 'rejected') throw c.reason
    if (b.status === 'rejected') throw b.reason
    res.cand = c.value
    res.base = b.value
  } catch (e) {
    res.error = String(e)
    return res
  } finally {
    gate(`${g.key}/both`).open(res)
  }
  if (g.noRerun || !res.base.length) return res
  const keep = tasks ? new Set(tasks) : undefined
  const restrict = (r: Rows) => keep ? new Map([...r].filter(([t]) => keep.has(t))) : r
  const D = new Set<string>()
  for (const v of views(g)) {
    const c = v.parse(res.cand, cand.path), bs = res.base.map(b => restrict(v.parse(b, base.path)))
    for (const t of differing(c, bs)) D.add(t)
  }
  res.differing = [...D].sort()
  if (!D.size || nReruns <= 0) return res
  if (D.size > 400) { res.error = `${D.size} tasks differ: not rerun (a broken candidate?)`; return res }
  if (!guard()) { res.error = 'the budget is spent: no reruns'; return res }
  log(`${g.key}: ${D.size} task(s) differ; ${nReruns} rerun(s) a side`)
  const reruns = (side: Side, tree: Tree) => Array.from({length: nReruns}, async (_, i) => {
    const p: Pass = {group: g.key, side, tree, dir: join(gd, `${side}-r${i + 1}`), tasks: res.differing}
    res.metas.push(await pass(g, p))
    res.reruns[side].push(p.dir)
  })
  await Promise.all([...reruns('cand', cand), ...reruns('base', base)])
  return res
}

// --------------------------------------------------------------------------------------------------------- spend
type Bill = {object_id: string, interval_start: string, cost: string}
function billing(since: Date): Bill[] {
  try { return JSON.parse(out0(['modal', 'billing', 'report', '--start', since.toISOString().slice(0, 10), '--resolution', 'h', '--json'])) as Bill[] } catch { return [] }
}
const spentBy = (apps: Set<string>, bills: Bill[]) => Math.round(bills.filter(b => apps.has(b.object_id)).reduce((s, b) => s + Number(b.cost), 0) * 1e4) / 1e4
function appsOf(outDir: string): Set<string> {
  const s = new Set<string>()
  const walk = (d: string) => { for (const f of readdirSync(d, {withFileTypes: true})) { if (f.isDirectory()) { if (!f.name.startsWith('run') && f.name !== 'pilots') walk(join(d, f.name)) } else if (f.name.endsWith('.meta.json')) for (const a of readJson<Meta>(join(d, f.name)).apps) s.add(a) } }
  if (existsSync(outDir)) walk(outDir)
  return s
}

// Modal reports an hour only once it is over, so between phases the guard reads an estimate: the task seconds the
// runners record, at $5.1e-5 a task-second for 2 vCPU and 4 GB (what Modal billed runs/chc7's CHC runs: $1.761 for
// 34,662 task-seconds, $1.5645 for 30,045), scaled by a job's cpu and memory.
function estimate(dir: string): number {
  let usd = 0
  const walk = (d: string) => {
    for (const f of readdirSync(d, {withFileTypes: true})) {
      const p = join(d, f.name)
      if (!f.isDirectory()) continue
      if (existsSync(join(p, 'results.jsonl'))) for (const l of readFileSync(join(p, 'results.jsonl'), 'utf8').split('\n').filter(Boolean)) { try { usd += Number((JSON.parse(l) as {seconds?: number}).seconds ?? 0) * 5.1e-5 } catch { /* a cut line */ } }
      else if (existsSync(join(p, 'summary.tsv'))) {
        const jobs = existsSync(`${p}.jobs.json`) ? new Map(readJson<Job[]>(`${p}.jobs.json`).map(j => [j.name, j])) : new Map<string, Job>()
        for (const l of readFileSync(join(p, 'summary.tsv'), 'utf8').split('\n').filter(Boolean)) {
          const [name, , secs] = l.split('\t'), j = jobs.get(name!)
          usd += Math.max(0, Number(secs)) * 5.1e-5 * (0.75 * (j?.cpu ?? 2) / 2 + 0.25 * (j?.memory ?? 4096) / 4096)
        }
      } else walk(p)
    }
  }
  if (existsSync(dir)) walk(dir)
  return Math.round(usd * 1e4) / 1e4
}

// ------------------------------------------------------------------------------------------------------- the size
function size(tree: string) {
  let bytes = 0, lines = 0
  const walk = (d: string) => { for (const f of readdirSync(d, {withFileTypes: true})) { const p = join(d, f.name); if (f.isDirectory()) { if (f.name !== 'generated' && f.name !== 'node_modules') walk(p) } else if (f.name.endsWith('.ts') && !f.name.endsWith('.test.ts')) { const t = readFileSync(p); bytes += t.length; lines += t.toString().split('\n').length - 1 } } }
  for (const d of ['core', 'kernel']) if (existsSync(join(tree, d))) walk(join(tree, d))
  return {bytes, lines}
}

// ----------------------------------------------------------------------------------------------------- the report
const fmt = (n: number) => Number.isInteger(n) ? n.toLocaleString('en-US') : n.toLocaleString('en-US', {maximumFractionDigits: 2})
const sign = (n: number) => (n > 0 ? '+' : '') + fmt(n)
function consensus(rs: Rows[]): Rows {
  const out: Rows = new Map()
  for (const t of new Set(rs.flatMap(r => [...r.keys()]))) {
    const os = rs.map(r => r.get(t)).filter((o): o is Obs => !!o), k = os.filter(o => o.solved).length
    out.set(t, {...(os.find(o => o.solved === k * 2 > os.length) ?? os[0]!), solved: k * 2 > os.length})
  }
  return out
}
function report(results: Result[], cand: Tree, base: Tree, outDir: string, t0: number, since: Date): string {
  const L: string[] = [], J: Record<string, unknown> = {}
  const p = (s = '') => L.push(s)
  p(`# The bar: ${cand.label} against ${base.label}`)
  p()
  p(`${quick ? 'Quick mode (each benchmark\'s dev set, gates/bar-dev.json)' : 'Full mode'}; backend ${backend}; the base ${together ? 'launched together' : `from the shared baseline (${nRuns} runs, ${cacheDir(base)})`}, except onecpu and g332 (always together); ${nReruns} rerun(s) a side of every task that differs. Started ${since.toISOString()}.`)
  p()
  const dev = devFile()
  for (const r of results) {
    const g = GROUPS.find(x => x.key === r.group)!
    if (r.error) p(`**${g.key}: ${r.error}**\n`)
    for (const m of r.metas.filter(x => x.retried?.length)) p(`- ${g.key}, a ${m.side} launch: ${m.retried!.length} task(s) failed on the backend and ran once more on Modal (${m.retried!.slice(0, 5).join(', ')}${m.retried!.length > 5 ? ', ...' : ''}).\n`)
    for (const m of r.metas.filter(x => x.code !== 0)) p(`**${g.key}: a ${m.side} launch exited ${m.code} after ${m.wall_s} s (${m.tasks === 'all' ? 'every task' : `${m.tasks} tasks`}); its log is beside its directory.**\n`)
    if (!r.cand) continue
    if (g.key === 'onecpu') { onecpu(r, p); continue }
    for (const v of views(g)) {
      const keep = r.quick ? new Set(r.quick) : undefined
      const restrict = (x: Rows) => keep ? new Map([...x].filter(([t]) => keep.has(t))) : x
      const c = v.parse(r.cand, cand.path), bs = r.base.map(b => restrict(v.parse(b, base.path)))
      if (!c.size && !bs.some(b => b.size)) continue
      const hc = v.headline(c), hb = bs.map(b => v.headline(b)), keys = Object.keys(hc)
      const mean = Object.fromEntries(keys.map(k => [k, hb.length ? Math.round(hb.reduce((s, h) => s + (h[k] ?? 0), 0) / hb.length * 100) / 100 : NaN]))
      p(`## ${v.title}${r.quick ? ` (${smoke ? 'smoke' : 'dev set'}: ${fmt(r.quick.length)} tasks)` : ''}`)
      p()
      p(`| side | ${keys.join(' | ')} |`)
      p(`| --- | ${keys.map(() => '---').join(' | ')} |`)
      p(`| candidate | ${keys.map(k => fmt(hc[k]!)).join(' | ')} |`)
      hb.forEach((h, i) => p(`| base run ${i + 1} | ${keys.map(k => fmt(h[k] ?? 0)).join(' | ')} |`))
      if (hb.length > 1) p(`| base mean | ${keys.map(k => fmt(mean[k]!)).join(' | ')} |`)
      if (hb.length) p(`| delta (candidate - base mean) | ${keys.map(k => sign(Math.round((hc[k]! - mean[k]!) * 100) / 100)).join(' | ')} |`)
      p()
      const sample = new Map<string, {cand: Obs[], base: Obs[]}>()
      const D = r.differing.filter(t => c.has(t))
      const rc = r.reruns.cand.map(d => v.parse(d, cand.path)), rb = r.reruns.base.map(d => v.parse(d, base.path))
      for (const t of D) sample.set(t, {cand: [c, ...rc].map(x => x.get(t)).filter((o): o is Obs => !!o), base: [...bs, ...rb].map(x => x.get(t)).filter((o): o is Obs => !!o)})
      const cmp = compareTasks(D, sample, v.limit)
      const n = (k: TaskCmp['kind'], f: (x: TaskCmp) => boolean = () => true) => cmp.filter(x => x.kind === k && f(x)).length
      if (g.key !== 'lean' && bs.length) {
        const outside = D.filter(t => !inBand(bs.map(b => b.get(t)).filter((o): o is Obs => !!o), v.limit))
        const only = (side: 'cand' | 'base') => D.filter(t => side === 'cand' ? !!c.get(t)?.solved : !c.get(t)?.solved).length
        p(`- ${fmt(D.length)} differ in the first pass (${only('cand')} solved by the candidate only, ${only('base')} by the base only; ${fmt(outside.length)} outside the base's noise band: its runs agreeing and no answer in the last quarter of the ${v.limit} s limit); after ${r.reruns.cand.length} rerun(s) a side:` +
          ` **gained ${n('gained')}** (${n('gained', x => x.solid)} in every run against none), **lost ${n('lost')}** (${n('lost', x => x.solid)} solid), noise ${n('noise')}, wrong ${n('wrong')}; answered only past ${0.75 * v.limit} s in some run (a flip at the time limit): ${cmp.filter(x => x.atLimit && x.kind === 'gained').length} of the gained, ${cmp.filter(x => x.atLimit && x.kind === 'lost').length} of the lost.`)
        if (r.quick && dev?.views[v.key]) {
          const pr = predict(dev.views[v.key]!, c, consensus(bs))
          p(`- Predicted full-set delta from the dev set: ${sign(pr.scaled)} (raw ${sign(pr.raw)} on ${fmt(Object.keys(dev.views[v.key]!.tasks).length)} tasks; calibration in gates/README.md).`)
        }
        const show = cmp.filter(x => x.kind !== 'noise').sort((a, b) => a.kind.localeCompare(b.kind) || a.task.localeCompare(b.task))
        if (show.length) {
          p()
          p('| task | verdict | candidate solved | base solved | at the limit | answers (candidate / base, seconds) |')
          p('| --- | --- | --- | --- | --- | --- |')
          const os = (xs: Obs[]) => xs.map(o => `${o.answer} ${fmt(Math.round(o.secs * 10) / 10)}`).join(', ')
          for (const x of show.slice(0, v.key === 'rw' || v.key.startsWith('suite') ? 400 : 120)) p(`| ${x.task} | ${x.kind}${x.solid ? ' (solid)' : ''} | ${x.cand} | ${x.base} | ${x.atLimit ? 'yes' : ''} | ${os(x.samples.cand)} / ${os(x.samples.base)} |`)
          if (show.length > 120 && v.key !== 'rw') p(`| ... ${show.length - 120} more in report.json | | | | | |`)
        }
        p()
        J[v.key] = {candidate: hc, base: hb, mean, differing: D.length, outsideBand: outside.length, tasks: cmp.map(x => ({task: x.task, kind: x.kind, solid: x.solid, atLimit: x.atLimit, inBand: x.inBand, cand: x.cand, base: x.base}))}
      } else J[v.key] = {candidate: hc}
      if (v.key === 'g332' && bs.length) g332(r, cand, base, p)
      if (v.key.startsWith('suite')) { const f = [...c].filter(([, o]) => !o.solved).map(([t]) => t); p(`- Failed on the candidate: ${f.length ? f.join(', ') : 'none'}.\n`) }
      if (v.key === 'lean') { const f = [...c].filter(([, o]) => !o.solved).map(([t]) => t); p(`- ${hc.checked} of ${hc.sampled} checked by Lean, at most ${fmt(hc.max_s!)} s a file${f.length ? `; not checked: ${f.join(', ')}` : ''}.\n`) }
    }
  }
  const sc = size(cand.path), sb = size(base.path)
  p('## Size')
  p()
  p(`core/ and kernel/ (.ts, tests excluded): ${fmt(sc.bytes)} bytes and ${fmt(sc.lines)} lines, against ${fmt(sb.bytes)} and ${fmt(sb.lines)} (${sign(sc.bytes - sb.bytes)} bytes, ${sign(sc.lines - sb.lines)} lines).`)
  p()
  const apps = appsOf(outDir), bills = billing(since)
  const own = spentBy(apps, bills)
  const madeNow = new Set<string>()
  for (const r of results) for (const d of r.base) if (d.startsWith(join(BAR, 'base')) && existsSync(`${d}.meta.json`) && new Date(readJson<Meta>(`${d}.meta.json`).started) >= since) for (const a of readJson<Meta>(`${d}.meta.json`).apps) madeNow.add(a)
  const baseDirs = results.flatMap(r => r.base.filter(d => madeNow.size && d.startsWith(join(BAR, 'base'))))
  const est = estimate(outDir) + baseDirs.filter(d => existsSync(`${d}.meta.json`) && new Date(readJson<Meta>(`${d}.meta.json`).started) >= since).reduce((s, d) => s + estimate(dirname(d)) / Math.max(1, readdirSync(dirname(d)).filter(x => /^run\d+$/.test(x)).length), 0)
  const lastHour = bills.map(b => b.interval_start).sort().at(-1) ?? 'none'
  const wall = Math.round((Date.now() - t0) / 1000)
  p('## Wall time and spend')
  p()
  p(`- Wall: ${fmt(wall)} s.`)
  p(`- Modal, billed for this bar's own ${apps.size} apps${madeNow.size ? ` and the ${madeNow.size} of the baseline runs it made` : ''}: $${fmt(own + spentBy(madeNow, bills))} (\`modal billing report --start ${since.toISOString().slice(0, 10)} --resolution h --json\`, complete hours only: the last reported starts ${lastHour}Z); estimated from the task seconds: $${fmt(Math.round(est * 100) / 100)}. \`bun gates/bar.ts spend ${outDir}\` reads the bill again once the hours are over.`)
  const metas = results.flatMap(r => r.metas), where = metas.map(m => JSON.stringify(m.where ?? null)).filter(w => w !== 'null')
  if (where.length) p(`- Where the jobs ran (each launch's backends.json): ${[...new Set(where)].join('; ')}.`)
  p()
  J.size = {cand: sc, base: sb}
  J.trees = {cand, base}
  J.started = since.toISOString()
  J.wall_s = wall
  J.spend = {own, apps: [...apps], baselineApps: [...madeNow], baselineMadeNow: spentBy(madeNow, bills), estimate: est, lastHour}
  J.results = results
  writeJson(join(outDir, 'report.json'), J)
  writeFileSync(join(outDir, 'REPORT.md'), L.join('\n') + '\n')
  return L.join('\n')
}
function onecpu(r: Result, p: (s?: string) => void) {
  const c = testTimes(r.cand!), b = r.base[0] ? testTimes(r.base[0]) : {tests: new Map<string, number[]>(), failed: []}
  const med = (xs: number[]) => { const s = [...xs].sort((x, y) => x - y); return s.length ? (s.length % 2 ? s[(s.length - 1) / 2]! : (s[s.length / 2 - 1]! + s[s.length / 2]!) / 2) : NaN }
  p('## The 5 s-limited tests on 1 vCPU')
  p()
  p(`Failed jobs: candidate ${c.failed.length ? c.failed.join(', ') : 'none'}; base ${b.failed.length ? b.failed.join(', ') : 'none'}. The ten slowest tests by their most on either side:`)
  p()
  p('| test | candidate median ms | candidate most ms | base median ms | base most ms | runs |')
  p('| --- | --- | --- | --- | --- | --- |')
  const keys = [...new Set([...c.tests.keys(), ...b.tests.keys()])].sort((x, y) => Math.max(...(b.tests.get(y) ?? [0]), ...(c.tests.get(y) ?? [0])) - Math.max(...(b.tests.get(x) ?? [0]), ...(c.tests.get(x) ?? [0])))
  for (const k of keys.slice(0, 10)) { const x = c.tests.get(k) ?? [], y = b.tests.get(k) ?? []; p(`| ${k} | ${fmt(med(x))} | ${fmt(Math.max(...x))} | ${fmt(med(y))} | ${fmt(Math.max(...y))} | ${x.length} / ${y.length} |`) }
  p()
}
function g332(r: Result, cand: Tree, base: Tree, p: (s?: string) => void) {
  const a = goals(r.cand!), b = goals(r.base[0]!)
  let same = 0
  const ratios: number[] = [], diff: string[] = []
  for (const [k, x] of a) { const y = b.get(k); if (!y) continue; if (goalSig(x) === goalSig(y)) same++; else diff.push(k); ratios.push(x.searchMs / Math.max(1, y.searchMs)) }
  ratios.sort((x, y) => x - y)
  const q = (f: number) => ratios.length ? ratios[Math.min(ratios.length - 1, Math.floor(f * ratios.length))]!.toFixed(3) : '-'
  const sum = (m: Map<string, {searchMs: number}>) => [...m.values()].reduce((s, g) => s + g.searchMs, 0)
  p(`- The same search (outcome, leaves, splits, CDCL's decisions, conflicts and nodes) on ${same} of ${a.size} goals (${cand.key} against ${base.key}); search ms summed ${fmt(sum(a))} against ${fmt(sum(b))}; candidate/base per goal p10 ${q(0.1)}, p50 ${q(0.5)}, p90 ${q(0.9)}${diff.length ? `; differ: ${diff.slice(0, 20).join(', ')}` : ''}.`)
  p()
}

// ------------------------------------------------------------------------------------------------------ commands
async function main() {
  if (sub === 'read') {
    const [v, ...dirs] = argv.filter((a, i) => !a.startsWith('--') && argv[i - 1] !== '--tree')
    for (const d of dirs) console.log(d, JSON.stringify(VIEWS[v!]!.headline(VIEWS[v!]!.parse(d, opt('tree', MAIN)))))
    return
  }
  if (sub === 'devset') return devsetCmd()
  if (sub === 'report') {
    // the report again from a run directory's report.json (after a fix, or once the bill is in)
    const dir = argv.find(a => !a.startsWith('--'))!, j = readJson<{results: Result[], trees?: {cand: Tree, base: Tree}, started?: string, wall_s: number}>(join(dir, 'report.json'))
    const shaOf = (side: Side) => j.results.flatMap(r => r.metas).find(m => m.side === side)?.sha ?? ''
    const t = (side: Side): Tree => j.trees?.[side] ?? {path: join(BAR, 'trees', shaOf(side).slice(0, 12)), sha: shaOf(side), key: shaOf(side).slice(0, 12), clean: true, label: shaOf(side).slice(0, 12)}
    const since = new Date(j.started ?? statSync(dir).birthtime)
    console.log(report(j.results, t('cand'), t('base'), dir, Date.now() - j.wall_s * 1000, since))
    return
  }
  if (sub === 'failed') { for (const d of argv.filter(a => !a.startsWith('--'))) console.log(d, backendFailed(d).length, backendFailed(d).slice(0, 3)); return }
  if (sub === 'compare') {
    // Run directories made elsewhere, compared as the bar compares its own: --group chc --cand d --base d1,d2
    // [--cand-reruns d,..] [--base-reruns d,..] [--cand-tree t] [--base-tree t] [--out dir]
    const g = GROUPS.find(x => x.key === opt('group'))!, list = (k: string) => opt(k) ? opt(k).split(',') : []
    const ct = {path: opt('cand-tree', MAIN), sha: '', key: 'cand', clean: true, label: opt('cand')}, bt = {path: opt('base-tree', MAIN), sha: '', key: 'base', clean: true, label: list('base').join(', ')}
    const r: Result = {group: g.key, cand: opt('cand'), base: list('base'), reruns: {cand: list('cand-reruns'), base: list('base-reruns')}, differing: [], metas: []}
    for (const v of views(g)) for (const t of differing(v.parse(r.cand!, ct.path), r.base.map(b => v.parse(b, bt.path)))) if (!r.differing.includes(t)) r.differing.push(t)
    const outDir = opt('out', join(BAR, 'compare', `${g.key}-${Date.now()}`))
    mkdir(outDir)
    console.log(report([r], ct, bt, outDir, Date.now(), new Date()))
    return
  }
  if (sub === 'spend') {
    const dir = argv.find(a => !a.startsWith('--'))!, j = readJson<{spend: {apps: string[], baselineApps?: string[]}}>(join(dir, 'report.json'))
    const t = readdirSync(dir).map(f => statSync(join(dir, f)).birthtime).sort((a, b) => +a - +b)[0] ?? new Date()
    const bills = billing(new Date(t.getTime() - 86_400_000))
    console.log(`${dir}: billed $${spentBy(new Set(j.spend.apps), bills)} for its ${j.spend.apps.length} apps, $${spentBy(new Set(j.spend.baselineApps ?? []), bills)} for the baseline runs it made; the last hour reported starts ${bills.map(b => b.interval_start).sort().at(-1) ?? 'none'}Z`)
    return
  }
  const only = opt('only', '') ? opt('only').split(',') : undefined
  for (const k of only ?? []) if (!GROUPS.some(g => g.key === k)) throw new Error(`no group ${k}: ${GROUPS.map(g => g.key).join(', ')}`)
  const base = treeOf(opt('base', 'main'))
  const t0 = Date.now(), since = new Date()
  if (sub === 'baseline') {
    const gs = GROUPS.filter(g => !g.candOnly && !g.pairAlways && (only ? only.includes(g.key) : true))
    const outDir = join(BAR, 'base', `${base.key}-${backend}-r${VERSION}`, 'pilots')
    const done = new Map<string, Promise<string[]>>()
    for (const g of gs) done.set(g.key, (g.after && done.get(g.after) ? done.get(g.after)! : Promise.resolve([])).then(() => baseline(g, base, nRuns, outDir)))
    const rs = await Promise.allSettled([...done.values()])
    rs.forEach((r, i) => log(`${gs[i]!.key}: ${r.status === 'fulfilled' ? `${r.value.length} run(s)` : String(r.reason)}`))
    const bills = billing(since), apps = new Set<string>()
    for (const g of gs) for (const d of readdirSync(join(cacheDir(base), g.key)).filter(x => x.startsWith('run'))) if (existsSync(join(cacheDir(base), g.key, `${d}.meta.json`))) for (const a of readJson<Meta>(join(cacheDir(base), g.key, `${d}.meta.json`)).apps) apps.add(a)
    log(`baseline ${cacheDir(base)}: ${Math.round((Date.now() - t0) / 1000)} s wall, $${spentBy(apps, bills)} on Modal for its ${apps.size} apps (modal billing report)`)
    reap()
    return
  }
  const cand = treeOf(opt('cand', resolve(HERE, '..')))
  const name = opt('name', `${cand.key}-vs-${base.key}-${quick ? 'quick' : 'full'}-${since.toISOString().slice(0, 16).replace(/[:T]/g, '')}`)
  const outDir = join(BAR, 'runs', name)
  mkdir(outDir)
  const gs = GROUPS.filter(g => only ? only.includes(g.key) : quick ? g.inQuick : true).filter(g => g.key !== 'lean' || !only || only.includes('its') || only.includes('lean'))
  log(`${cand.label} against ${base.label}: ${gs.map(g => g.key).join(', ')} -> ${outDir}`)
  let over = false
  const guard = () => {
    if (over) return false
    const s = Math.max(estimate(outDir), spentBy(appsOf(outDir), billing(since)))
    if (s > budget) { over = true; log(`spend $${s} (estimate, or billed where larger) is past the budget $${budget}`) }
    return !over
  }
  const watch = setInterval(() => { if (!guard()) void stopAll(`the budget $${budget} is spent`) }, 300_000)
  try {
    if (gs.some(g => g.key === 'lean') && !gs.some(g => g.key === 'its')) gs.unshift(GROUPS.find(g => g.key === 'its')!)
    const inRun = new Set(gs.map(g => g.key))
    const results = await Promise.all(gs.map(g => groupFlow(g, cand, base, outDir, guard, inRun)))
    clearInterval(watch)
    await Bun.sleep(5000)
    reap()
    console.log(report(results, cand, base, outDir, t0, since))
    log(`report: ${join(outDir, 'REPORT.md')}`)
  } finally {
    clearInterval(watch)
    if (live.size) await stopAll('the bar is ending')
  }
}

// The dev sets: for each view, from the first run of a base's shared baseline, `devSet`'s stratified sample; the
// pilots are the reference run's two fastest solved tasks.
function devsetCmd() {
  const key = opt('from', '') || readdirSync(join(BAR, 'base')).sort().at(-1)!
  const root = join(BAR, 'base', key), sha = key.split('-')[0]!
  const tree = existsSync(join(BAR, 'trees', sha)) ? join(BAR, 'trees', sha) : MAIN
  // (the sizes from gates/bar-calibrate.ts on every past pair: CHC's prediction error 7.9 tasks at 257, 2.5 at 700)
  const SIZES: Record<string, number> = {chc: 700, its: 400, 'its-scc': 120, sv: 140, 'sv-scc': 40, tip: 250, f1: 50, f2: 40, rw: 90}
  const d: DevFile = {made: `from runs/bar/base/${key} (${new Date().toISOString().slice(0, 10)})`, views: {}, pilot: {}}
  for (const g of GROUPS) for (const v of views(g)) {
    if (!SIZES[v.key] || !existsSync(join(root, g.key, 'run1'))) continue
    const ref = v.parse(join(root, g.key, 'run1'), tree)
    const dev = devSet(v, ref, SIZES[v.key]!, `${key}/${g.key}/run1`)
    d.views[v.key] = dev
    if (!d.pilot[g.key]) d.pilot[g.key] = [...ref].filter(([, o]) => o.solved).sort((a, b) => a[1].secs - b[1].secs).slice(0, g.key === 'g332' ? 1 : 2).map(([t]) => t)
    log(`${v.key}: ${dev.size} of ${dev.of} (${Object.keys(dev.strata).length} strata)`)
  }
  for (const s of ['suite']) if (existsSync(join(root, s, 'run1'))) d.pilot[s] = d.pilot['suite-usual'] = [...VIEWS.suite!.parse(join(root, s, 'run1'), tree)].filter(([, o]) => o.solved).sort((a, b) => a[1].secs - b[1].secs).slice(0, 1).map(([t]) => t)
  if (flag('write')) writeJson(DEV_FILE, d)
  else console.log(JSON.stringify({views: Object.fromEntries(Object.entries(d.views).map(([k, v]) => [k, {size: v.size, of: v.of}])), pilot: d.pilot}, null, 1))
}

await main().catch(async (e: unknown) => {
  console.error(e)
  await stopAll('an error')
  process.exit(1)
})
