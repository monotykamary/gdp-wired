// The Lean conformance through the interchange format as jobs (supercomputer run): each writes its kinds' documents
// (interchange/lean.ts write), reads them back in another process, checks them and emits Lean (emit), and runs Lean on
// each file (through the axiom gate, scripts/lean-gate), printing per file its exit code and the number of claims in it. A file elaborates exactly when Lean computes
// the checker's answer on every claim.
// The ix-lean-suite-* jobs do the same with the suites' own certificates: suite jobs run with interchange/capture.ts
// preloaded (as interchange/suite-jobs.ts runs them), interchange/verify.ts tampers each accepted document three ways,
// and lean.ts pick takes up to --per documents of each kind Lean checks here, with their twins, for emit.
//   bun interchange/lean-jobs.ts > jobs.json && supercomputer run --jobs jobs.json --out <runs dir>
import {readFileSync} from 'node:fs'
import {join} from 'node:path'

const lib = 'Cert Kernel Progress StepLaw Steps Sets Live KInd NonTerm Rationals Cyclic Data'
const job = (name: string, produce: string[], files: string[]) => ({
  name: `ix-lean-${name}`, cwd: '.', cpu: 4.0, memory: 8192, timeout: 3600,
  cmd: [
    'export PATH=$PWD/scripts/lean-gate:$PATH; cd lean-kernel && export LEAN_PATH=$PWD:$(dirname $(dirname $(readlink -f $(elan which lean))))/lib/lean',
    `for f in ${lib}; do { [ -f $f.olean ] || lean -o $f.olean $f.lean; } > /dev/null 2>&1 || { echo build-failed $f; exit 1; }; done; cd ..`,
    'W=/tmp/ix-lean; rm -rf $W',
    ...produce,
    'bun interchange/lean.ts emit $W/docs $W/lean || exit 1',
    'ls $W/docs | wc -l',
    `cd lean-kernel; s=0; for f in ${files.join(' ')}; do cp $W/lean/$f.lean .; ( time lean $f.lean ) > $f.out 2>&1; e=$?; [ $e -eq 0 ] || s=1; echo "$f: lean exit $e, $(grep -c -e '^example' -e '^theorem' -e '^namespace' $f.lean) claims, $(wc -c < $f.lean) bytes"; grep -A6 'error' $f.out | head -30; tail -4 $f.out; done; echo lean-exit $s; exit $s`,
  ].join('\n'),
})
const none = '--nonterm 0 --kind 0 --rationals 0 --goals 0 --cyclic 0 --rings 0'
const only = (o: Record<string, number>) => none.replace(/--(\w+) 0/g, (m, k: string) => (k in o ? `--${k} ${o[k]}` : m))
const write = (o: Record<string, number>) => [`bun interchange/lean.ts write $W/docs ${only(o)} || exit 1`]

// The suites' certificates: the named suite jobs under the capture, then verify's twins, then pick.
type Job = {name: string, cmd: string, cwd?: string}
const suite = JSON.parse(readFileSync(join(import.meta.dir, '..', 'supercomputer', 'suite.json'), 'utf8')) as Job[]
const captured = (names: string[], per: number) => [
  'bun install --frozen-lockfile >/dev/null 2>&1; R=$PWD; C=/tmp/ixl-capture; K=/tmp/ixl-verify; rm -rf $C $K',
  'bun interchange/build.ts > /tmp/ixl-build.log 2>&1 || { cat /tmp/ixl-build.log; exit 1; }; head -3 /tmp/ixl-build.log',
  'bun() { case "$1" in test) shift; command bun test --preload "$R/interchange/capture.ts" "$@";; *.ts|*.js|*/*.ts) command bun --preload "$R/interchange/capture.ts" "$@";; *) command bun "$@";; esac; }; export -f bun',
  ...names.map(n => { const j = suite.find(x => x.name === n); if (!j) throw new Error(`no suite job ${n}`); return `( export GDP_CAPTURE=$C; cd ${JSON.stringify(j.cwd ?? '.')} && ${j.cmd} ) > /tmp/ixl-job.log 2>&1; echo "suite job ${n}: exit $?"` }),
  'unset -f bun',
  'bun interchange/verify.ts $C --tamper --keep $K > /tmp/ixl-verify.log 2>&1; grep -E "^(kind|TOTAL|tampered|disagreements|capture)" /tmp/ixl-verify.log',
  `bun interchange/lean.ts pick $W/docs $C $K/tampered --per ${per} || exit 1`,
]
const files = ['IxGoals', 'IxRat', 'IxNonTerm', 'IxCyclic', 'IxCyclicByValue', 'IxKind']
console.log(JSON.stringify([
  job('nonterm-rat-rings', write({nonterm: 40, rationals: 150, rings: 24}), ['IxNonTerm', 'IxRat', 'IxRings']),
  job('kind', write({kind: 24}), ['IxKind']),
  job('goals-cyclic', write({goals: 40, cyclic: 40}), ['IxGoals', 'IxCyclic', 'IxCyclicByValue']),
  job('suite-examples', captured(['readme', 'examples-finance', 'examples-access'], 30), files),
  job('suite-kernel', captured(['tamper-refusals', 'steplaw', 'conformance-1'], 40), files),
  job('suite-rat-nonterm-kind', captured(['rationals', 'nonterm', 'kinduction', 'cyclic'], 40), files),
], null, 1))
