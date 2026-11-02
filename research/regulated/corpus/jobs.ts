// The corpus as a batch for the supercomputer: one job per item (run.ts), its record printed in the job's log.
//   bun research/regulated/corpus/jobs.ts [--items <dir>] [--ms 60000] > jobs.json
//   supercomputer run --jobs jobs.json --out runs/regulated/<name> --class gate --data research/regulated/corpus/.cache:research/regulated/corpus/.cache
//   bun research/regulated/corpus/collect.ts runs/regulated/<name>
import {itemsIn} from './fetch.ts'

const argv = process.argv.slice(2), opt = (k: string, d: string) => (argv.includes(`--${k}`) ? argv[argv.indexOf(`--${k}`) + 1]! : d)
const items = opt('items', 'research/regulated/corpus/items'), ms = opt('ms', '60000')
console.log(JSON.stringify(itemsIn(items).map(it => ({name: it.name, cpu: 2, timeout: 3600,
  cmd: `bun install --frozen-lockfile > /dev/null 2>&1; bun research/regulated/corpus/run.ts ${it.name} --items ${items} --out /tmp/regulated --ms ${ms}`})), null, 1))
