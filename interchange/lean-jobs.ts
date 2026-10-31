// The Lean conformance through the interchange format as jobs (supercomputer/run.py): each writes its kinds' documents
// (interchange/lean.ts write), reads them back in another process, checks them and emits Lean (emit), and runs Lean on
// each file, printing per file its exit code and the number of claims in it. A file elaborates exactly when Lean computes
// the checker's answer on every claim.
//   bun interchange/lean-jobs.ts > jobs.json && python3 supercomputer/run.py --jobs jobs.json --out <runs dir>
const lib = 'Cert Kernel Progress StepLaw Steps Sets Live KInd NonTerm Rationals Cyclic Data'
const job = (name: string, counts: string, files: string[]) => ({
  name: `ix-lean-${name}`, cwd: '.', cpu: 4.0, memory: 8192, timeout: 3600,
  cmd: [
    'cd lean-kernel && export LEAN_PATH=$PWD:$(dirname $(dirname $(readlink -f $(elan which lean))))/lib/lean',
    `for f in ${lib}; do { [ -f $f.olean ] || lean -o $f.olean $f.lean; } > /dev/null 2>&1 || { echo build-failed $f; exit 1; }; done; cd ..`,
    'W=/tmp/ix-lean; rm -rf $W',
    `bun interchange/lean.ts write $W/docs ${counts} && bun interchange/lean.ts emit $W/docs $W/lean || exit 1`,
    'ls $W/docs | wc -l',
    `cd lean-kernel; s=0; for f in ${files.join(' ')}; do cp $W/lean/$f.lean .; ( time lean $f.lean ) > $f.out 2>&1; e=$?; [ $e -eq 0 ] || s=1; echo "$f: lean exit $e, $(grep -c -e '^example' -e '^theorem' -e '^namespace' $f.lean) claims, $(wc -c < $f.lean) bytes"; grep -A6 'error' $f.out | head -30; tail -4 $f.out; done; echo lean-exit $s; exit $s`,
  ].join('\n'),
})
const none = '--nonterm 0 --kind 0 --rationals 0 --goals 0 --cyclic 0 --rings 0'
const only = (o: Record<string, number>) => none.replace(/--(\w+) 0/g, (m, k: string) => (k in o ? `--${k} ${o[k]}` : m))
console.log(JSON.stringify([
  job('nonterm-rat-rings', only({nonterm: 40, rationals: 150, rings: 24}), ['IxNonTerm', 'IxRat', 'IxRings']),
  job('kind', only({kind: 24}), ['IxKind']),
  job('goals-cyclic', only({goals: 40, cyclic: 40}), ['IxGoals', 'IxCyclic', 'IxCyclicByValue']),
], null, 1))
