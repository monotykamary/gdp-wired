// Read-only, event-driven lane notification; never edits another worktree or merges.
import {watch} from 'node:fs'
import {resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
const refs=['main','claude/mldr-gen','claude/track-mldr','claude/mldr-incl','claude/mldr-wall','claude/mldr-leaves']
const git=(...args:string[])=>{const r=spawnSync('git',args,{encoding:'utf8'});if(r.status!==0)throw Error(r.stderr);return r.stdout.trim()}
const snapshot=()=>Object.fromEntries(refs.map(ref=>[ref,git('rev-parse',ref)]))
const initial=snapshot(), common=resolve(git('rev-parse','--git-common-dir'))
console.log('LANE_I_WATCH_START '+JSON.stringify(initial))
const watchers:ReturnType<typeof watch>[]=[], deadline=setTimeout(()=>finish('timeout'),Number(process.argv[2]??600)*1000)
let ended=false, pending:ReturnType<typeof setTimeout>|undefined
function finish(reason:string){if(ended)return;ended=true;clearTimeout(deadline);if(pending)clearTimeout(pending);for(const w of watchers)w.close();console.log('LANE_I_WATCH_END '+JSON.stringify({reason,initial,current:snapshot()}))}
const changed=()=>{if(pending)clearTimeout(pending);pending=setTimeout(()=>{const now=snapshot();if(refs.some(ref=>now[ref]!==initial[ref]))finish('changed')},100)}
for(const dir of ['refs/heads','refs/heads/claude'])watchers.push(watch(resolve(common,dir),changed))
process.once('SIGTERM',()=>finish('stopped'));process.once('SIGINT',()=>finish('stopped'))
changed()
