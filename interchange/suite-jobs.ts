// The release suite's jobs (modal/suite.json, those that aren't Lean's or the type check) with their certificates
// captured and checked again: each job builds the checker (the bundle and the WebAssembly module, interchange/tools.sh's
// Javy and Wasmtime), runs its command with interchange/capture.ts preloaded into every bun it starts, then
// interchange/verify.ts over what it took (tampered twins, the WebAssembly module, the second checker), printing the
// summary after SUMMARY-JSON. interchange/aggregate.ts sums the logs.
//   bun interchange/suite-jobs.ts > jobs.json && python3 modal/run.py --jobs jobs.json --out <runs dir> [--usual]
import {readFileSync} from 'node:fs'
import {join} from 'node:path'

type Job = {name: string, cmd: string, cwd?: string, cpu?: number, memory?: number, timeout?: number}
// (and the examples no suite job runs: the guide's and the wide rule's)
const jobs = [...JSON.parse(readFileSync(join(import.meta.dir, '..', 'modal', 'suite.json'), 'utf8')) as Job[], {name: 'examples-rest', cmd: 'bun examples/guide.ts 2>&1 && bun examples/wide.ts 2>&1', cwd: '.', timeout: 900}]
const only = process.argv[2] ? new RegExp(process.argv[2]) : undefined
const wrap = (j: Job): Job => ({
  name: `ix-${j.name}`, cwd: '.', ...(j.cpu ? {cpu: j.cpu} : {}), ...(j.memory ? {memory: j.memory} : {}), timeout: (j.timeout ?? 900) + 1200,
  cmd: [
    'R=$PWD; T=/tmp/gdp-tools; C=/tmp/ix-capture; rm -rf $C',
    'sh interchange/tools.sh $T >/dev/null && JAVY=$T/javy bun interchange/build.ts --wasm > /tmp/ix-build.log 2>&1 && cat /tmp/ix-build.log || { echo BUILD FAILED; cat /tmp/ix-build.log; exit 1; }',
    // every bun the command starts (a script or a test run) with the capture preloaded
    'bun() { case "$1" in test) shift; command bun test --preload "$R/interchange/capture.ts" "$@";; *.ts|*.js|*/*.ts) command bun --preload "$R/interchange/capture.ts" "$@";; *) command bun "$@";; esac; }; export -f bun',
    `export GDP_CAPTURE=$C; ( cd ${JSON.stringify(j.cwd ?? '.')} && ${j.cmd} ) > /tmp/ix-job.log 2>&1; code=$?; tail -c 3000 /tmp/ix-job.log; echo "JOB EXIT $code"`,
    'unset -f bun; unset GDP_CAPTURE; { python3 -m pip install -q jsonschema==4.23.0 || python3 -m pip install -q --break-system-packages jsonschema==4.23.0; } > /dev/null 2>&1',
    'bun interchange/verify.ts $C --tamper --wasm "$T/wasmtime run" --python python3 --schema python3 --out /tmp/ix-verify.json; echo SUMMARY-JSON; cat /tmp/ix-verify.json',
  ].join('\n'),
})
console.log(JSON.stringify(jobs.filter(j => !j.name.startsWith('lean') && j.name !== 'check' && (!only || only.test(j.name))).map(wrap), null, 1))
