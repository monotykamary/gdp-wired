// The Solidity front end (core/extract-sol.ts) on small contracts, each checked against its bytecode on anvil: a ledger's
// laws proven (two cells written in one transfer, unchecked arithmetic at a symbolic 2^256), the DAO's re-entrancy
// broken by a run replayed on the code and its fixes proven, a wrap past 2^256 broken only where it is one, and what the
// subset refuses. Needs solc 0.8 and anvil (research/sol/sol-setup.sh); skipped without them.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, readFileSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {checkTarget, runOf} from './cli.ts'
import {proveRule} from './dsl.ts'
import {buildLaw, lawsIn} from './laws.ts'
import {extractSolidity} from './extract-sol.ts'

const has = (c: string) => { try { execFileSync(c, ['--version'], {stdio: 'ignore'}); return true } catch { return false } }
const t = has('solc') && has('anvil') ? test : test.skip
const dir = mkdtempSync(`${tmpdir()}/gdp-sol-test-`)
const file = (name: string, body: string) => { const f = `${dir}/${name}.sol`; writeFileSync(f, `// SPDX-License-Identifier: MIT\npragma solidity ^0.8.20;\n${body}`); return f }
const verdicts = async (f: string, entry?: string) => {
  const [r] = await checkTarget({lang: 'solidity', at: f, files: [f]}, {ms: 60_000, propose: false, ...(entry ? {entry} : {})})
  expect(r!.refusals).toEqual([])
  for (const law of r!.laws) {
    expect(law).toMatchObject({verdict: 'unknown', translation: 'unchecked'})
    expect(law.run).toBeUndefined()
    expect(law.replayed).toBeUndefined()
    expect(law.cert).toBeUndefined()
  }
  return Object.fromEntries(r!.laws.map(l => [l.name, l]))
}

// A model counterexample and its bytecode replay remain useful independent
// evidence. They must not be manufactured into a native-law source verdict.
const modelAndReplay = (f: string, name: string, broken: boolean) => {
  const x = extractSolidity(f)
  expect(x.ok).toBe(true)
  const law = lawsIn(readFileSync(f, 'utf8')).find(l => l.name === name)!
  const built = buildLaw(x, law)
  if (built.kind !== 'law') throw Error('expected a state invariant')
  const model = proveRule(x.rule!, [...x.invariants ?? [], built.law], {search: {ms: 60_000}})
  expect(model).toMatchObject({proven: false, checked: false, translation: 'unchecked'})
  if (!broken) return {run: model.run ? runOf(x, model.run) : undefined, replayed: undefined}
  expect(model.kernelProven).toBe(false)
  expect(model.run).toBeDefined()
  const replay = x.replay!(model.run!, built.law)
  expect(replay.ok).toBe(true)
  return {run: runOf(x, model.run!), replayed: replay.what}
}

const VAULT = (fixed: boolean) => `
/// gdp: law the vault holds what it owes: balance >= sum(balances)
contract Vault {
    mapping(address => uint256) public balances;
    function deposit() external payable { balances[msg.sender] += msg.value; }
    function withdraw() external {
        uint256 amount = balances[msg.sender];
        ${fixed ? 'balances[msg.sender] = 0;' : ''}
        (bool ok, ) = msg.sender.call{value: amount}("");
        require(ok, "send failed");
        ${fixed ? '' : 'balances[msg.sender] = 0;'}
    }
}`

t('a ledger: the balances sum to the supply, a transfer never mints (two cells in one step, unchecked)', async () => {
  const v = await verdicts(file('Ledger', `
/// gdp: law the balances sum to the supply: sum(balances) == totalSupply
contract Ledger {
    mapping(address => uint256) public balances;
    uint256 public totalSupply;
    function mint(address to, uint256 amount) external { totalSupply += amount; balances[to] += amount; }
    /// gdp: law transfer never mints: totalSupply == old(totalSupply)
    function transfer(address to, uint256 amount) external {
        uint256 b = balances[msg.sender];
        require(b >= amount);
        unchecked { balances[msg.sender] = b - amount; }
        balances[to] += amount;
    }
}`))
  expect(v['the balances sum to the supply']!.kernelProven).toBe(true)
  expect(v['transfer never mints']!.kernelProven).toBe(true)
}, 600_000)

t('the DAO\'s shape: broken by a re-entrant run, replayed on the code; cleared first, proven', async () => {
  const badFile = file('VaultBad', VAULT(false))
  const bad = (await verdicts(badFile))['the vault holds what it owes']!
  expect(bad.kernelProven).toBe(false)
  const concrete = modelAndReplay(badFile, 'the vault holds what it owes', true)
  expect(concrete.replayed).toMatch(/replayed on the code.*calls made from inside another/)
  expect(concrete.run!.some(s => s.includes('withdraw$resume'))).toBe(true)
  expect((await verdicts(file('VaultGood', VAULT(true))))['the vault holds what it owes']!.kernelProven).toBe(true)
}, 900_000)

t('a lock held across the call: re-entering withdraw reverts, the law proven', async () => {
  const guarded = file('Guarded', `
/// gdp: law the vault holds what it owes: balance >= sum(balances)
contract Guarded {
    mapping(address => uint256) public balances;
    bool locked;
    modifier noReentrant() { require(!locked, "re-entered"); locked = true; _; locked = false; }
    function deposit() external payable { balances[msg.sender] += msg.value; }
    function withdraw() external noReentrant {
        uint256 amount = balances[msg.sender];
        (bool ok, ) = msg.sender.call{value: amount}("");
        require(ok);
        balances[msg.sender] = 0;
    }
}`)
  await verdicts(guarded)
  expect(modelAndReplay(guarded, 'the vault holds what it owes', false).run).toBeUndefined()
}, 900_000)

t('a wrap past 2^256: unchecked, a counter below its start is reached; checked, never', async () => {
  const src = (unchecked: boolean) => `
/// gdp: law never below the start: count >= 0 and count <= 100
contract Counter {
    uint256 public count;
    function down() external { ${unchecked ? 'unchecked { count -= 1; }' : 'count -= 1;'} }
    function up() external { require(count < 100); count += 1; }
}`
  const wrapped = file('Wraps', src(true))
  expect((await verdicts(wrapped))['never below the start']!.kernelProven).toBe(false)
  expect(modelAndReplay(wrapped, 'never below the start', true).replayed).toContain('replayed on the code')
  expect((await verdicts(file('Reverts', src(false))))['never below the start']!.kernelProven).toBe(true)
}, 900_000)

t('refused, each where it is with why', () => {
  const why = (name: string, body: string) => { const x = extractSolidity(file(name, body)); expect(x.ok).toBe(false); return x.refusals[0]!.what }
  expect(why('Loop', 'contract Loop { uint256 x; function f(uint256 n) external { for (uint256 i; i < n; i++) x += 1; } }')).toMatch(/a loop/)
  expect(why('Order', 'contract Order { address a; function f(address b) external { require(a < b); a = b; } }')).toMatch(/addresses ordered/)
  expect(why('Other', 'interface T { function g() external; }\ncontract Other { uint256 x; function f(address t) external { T(t).g(); x = 1; } }')).toMatch(/another contract/)
  expect(why('Big', 'contract Big { uint256 x; function f() external { x = 1e18; } }')).toMatch(/past the rule's 2\^53/)
}, 300_000)

// The check's harness failing (anvil's transport: a transaction sent, its answer lost, as under a loaded machine) is
// the check's outcome, never a difference nor a pass: the check runs once more from a fresh harness, and a second
// failure says so. The transport broken here by a proxy in front of anvil (GDP_ANVIL), dropping the answer to the
// FAULT_N-th transaction it forwards: in every harness, or only the first (FAULT_ONCE, a file it makes).
const PROXY = `import http.server, json, os, socket, subprocess, sys, urllib.request
args = sys.argv[1:]; port = int(args[args.index('--port') + 1])
with socket.socket() as s: s.bind(('127.0.0.1', 0)); up = s.getsockname()[1]
real = list(args); real[real.index('--port') + 1] = str(up)
subprocess.Popen(['sh', '-c', 'anvil "$@" & a=$!; while kill -0 ' + str(os.getpid()) + ' 2>/dev/null; do sleep 0.5; done; kill $a', 'sh', *real])
n, once = int(os.environ.get('FAULT_N', '0')), os.environ.get('FAULT_ONCE')
seen = [0]
class H(http.server.BaseHTTPRequestHandler):
  def log_message(self, *a): pass
  def do_POST(self):
    body = self.rfile.read(int(self.headers['content-length']))
    req = json.loads(body)
    sends = sum(1 for x in (req if isinstance(req, list) else [req]) if x.get('method') == 'eth_sendTransaction')
    out = urllib.request.urlopen(urllib.request.Request(f'http://127.0.0.1:{up}', data=body, headers={'content-type': 'application/json'}), timeout=60).read()
    seen[0] += sends
    if sends and seen[0] == n and not (once and os.path.exists(once)):
      if once: open(once, 'w').close()
      self.close_connection = True
      self.connection.shutdown(socket.SHUT_RDWR)
      return
    self.send_response(200); self.send_header('content-type', 'application/json'); self.send_header('content-length', str(len(out))); self.end_headers(); self.wfile.write(out)
http.server.ThreadingHTTPServer(('127.0.0.1', port), H).serve_forever()
`
t('the check\'s harness failing (anvil\'s transport) is retried once, then the check\'s own outcome: never a difference', () => {
  const proxy = `${dir}/fault-anvil.py`
  writeFileSync(proxy, PROXY)
  writeFileSync(`${dir}/fault-anvil`, `#!/bin/sh\nexec python3 ${proxy} "$@"\n`)
  execFileSync('chmod', ['+x', `${dir}/fault-anvil`])
  const f = file('Mint', 'contract Mint {\n    uint256 public totalSupply;\n    function mint(uint256 amount) external { totalSupply += amount; }\n}')
  const run = (env: Record<string, string>) => {
    const old = {...process.env}
    Object.assign(process.env, env)
    try { return extractSolidity(f, {anvil: `${dir}/fault-anvil`, check: {runs: 6, depth: 4, states: 6}}) } finally { for (const k of Object.keys(env)) if (old[k] === undefined) delete process.env[k]; else process.env[k] = old[k] }
  }
  const twice = run({FAULT_N: '3'})
  expect(twice.ok).toBe(false)
  expect(twice.refusals[0]!.what).toMatch(/^the check's harness failed, twice \(a request past its time or its transport, not the code\): .*(RemoteDisconnected|Connection|closed)/)
  expect(twice.refusals[0]!.what).not.toMatch(/the rule and the code differ/)
  const once = run({FAULT_N: '3', FAULT_ONCE: `${dir}/fault-once`})
  expect(once.refusals).toEqual([])
  expect(once.ok).toBe(true)
}, 600_000)

// The reader fuzz's misread (core/extract-fuzz.ts): a call into other code whose failure the function goes on past
// (no require(ok)): the EVM undoes what the callee did, its calls back included, which the re-entrant rule can't.
t('a call into other code whose failure the function goes on past: refused (re-entrancy)', () => {
  const x = extractSolidity(file('NoCheck', VAULT(false).replace('require(ok, "send failed");', '')))
  expect(x.ok).toBe(false)
  expect(x.refusals[0]!.what).toMatch(/re-entrancy: withdraw: a call into other code whose failure the function goes on past/)
}, 600_000)

// anvil's state on disk (boat's disks filled with ~/.foundry/anvil/tmp from killed runs): the harness keeps anvil's in a
// directory of its own, gdp-anvil-<pid>-*, which a killed harness's watchdog removes, and removes at start what killed
// runs before it left (their directories, anvil's old state folders).
t('a killed harness leaves no anvil state behind; what killed runs left is removed at start', async () => {
  const {existsSync, mkdirSync, readdirSync, utimesSync} = await import('node:fs')
  const home = mkdtempSync(`${tmpdir()}/gdp-solhome-`), legacy = `${home}/.foundry/anvil/tmp`
  mkdirSync(`${legacy}/old-state`, {recursive: true}); mkdirSync(`${legacy}/new-state`, {recursive: true})
  utimesSync(`${legacy}/old-state`, Date.now() / 1000 - 3 * 3600, Date.now() / 1000 - 3 * 3600)
  const dead = `${tmpdir()}/gdp-anvil-999999999-left`
  mkdirSync(dead, {recursive: true})
  const harness = new URL('./sol/harness.py', import.meta.url).pathname
  const p = Bun.spawn(['python3', '-c', `import sys, time; sys.path.insert(0, ${JSON.stringify(harness.replace(/\/[^/]*$/, ''))}); import harness; harness.start_anvil(); print(harness.S['anvil_dir'], flush=True); time.sleep(600)`], {stdout: 'pipe', env: {...process.env, HOME: home}})
  const reader = p.stdout.getReader(), {value} = await reader.read()
  const d = new TextDecoder().decode(value).trim()
  expect(existsSync(d)).toBe(true)
  expect(existsSync(dead)).toBe(false)
  expect(readdirSync(legacy)).toEqual(['new-state'])
  p.kill(9)
  for (let i = 0; i < 40 && existsSync(d); i++) await Bun.sleep(250)
  expect(existsSync(d)).toBe(false)
  expect(readdirSync(tmpdir()).filter(n => n.startsWith(`gdp-anvil-${p.pid}-`))).toEqual([])
}, 120_000)
