// The refuted laws' runs on the real code: each project's file fetched at its pin (research/embedded/corpus/run.ts's
// fetch), compiled as it ships beside a driver that takes the run the CLI gave, and run.
//   bun research/embedded/repro/run.ts     (clang and clang++ on the PATH)
// (the C driver is .c.in: the boat tree ships no .c files)
import {execFileSync} from 'node:child_process'
import {join} from 'node:path'
import {ITEMS} from '../corpus/items.ts'
import {fetchItem} from '../corpus/run.ts'

const HERE = import.meta.dir, shims = join(HERE, '../corpus/shims')
const cases: {item: string, src: string, cpp: boolean, flags: (tree: string) => string[]}[] = [
  {item: 'makair-alarm', src: 'makair-alarm.cpp', cpp: true, flags: t => ['-std=c++17', `-I${t}`, `-I${join(shims, 'makair')}`]},
  {item: 'px4-arming', src: 'px4-arming.cpp', cpp: true, flags: t => ['-std=c++17', `-I${t}`, `-I${join(shims, 'px4')}`, `-I${join(t, 'src/modules/commander/Arming/ArmStateMachine')}`]},
  {item: 'canopen-node-guarding', src: 'canopen-node-guarding.c.in', cpp: false, flags: t => [`-I${t}`, `-I${t}/example`, '-DCO_CONFIG_NODE_GUARDING=0x01']},
]
for (const c of cases) {
  const it = ITEMS.find(i => i.id === c.item)!, tree = fetchItem(it), exe = `/tmp/gdp-repro-${c.item}`
  // (PX4: its checks' header, the stand-in the corpus reads it with)
  if (c.item === 'px4-arming') { const d = join(tree, 'src/modules/commander/HealthAndArmingChecks'); execFileSync('mkdir', ['-p', d]); execFileSync('cp', [join(shims, 'px4/HealthAndArmingChecks.hpp'), d]) }
  execFileSync(c.cpp ? 'clang++' : 'clang', [...c.flags(tree), '-w', '-x', c.cpp ? 'c++' : 'c', join(HERE, c.src), '-o', exe, ...(process.platform === 'linux' ? ['-Wl,--unresolved-symbols=ignore-all'] : ['-Wl,-undefined,dynamic_lookup'])])
  process.stdout.write(`== ${c.item} (${it.repo} @ ${it.commit})\n${execFileSync(exe, {encoding: 'utf8'})}`)
}
