// The Solidity front end (core/extract-sol.ts) on small contracts, each checked against its bytecode on anvil: a ledger's
// laws proven (two cells written in one transfer, unchecked arithmetic at a symbolic 2^256), the DAO's re-entrancy
// broken by a run replayed on the code and its fixes proven, a wrap past 2^256 broken only where it is one, and what the
// subset refuses. Needs solc 0.8 and anvil (research/sol/sol-setup.sh); skipped without them.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {checkTarget} from './cli.ts'
import {extractSolidity} from './extract-sol.ts'

const has = (c: string) => { try { execFileSync(c, ['--version'], {stdio: 'ignore'}); return true } catch { return false } }
const t = has('solc') && has('anvil') ? test : test.skip
const dir = mkdtempSync(`${tmpdir()}/gdp-sol-test-`)
const file = (name: string, body: string) => { const f = `${dir}/${name}.sol`; writeFileSync(f, `// SPDX-License-Identifier: MIT\npragma solidity ^0.8.20;\n${body}`); return f }
const verdicts = async (f: string, entry?: string) => {
  const [r] = await checkTarget({lang: 'solidity', at: f, files: [f]}, {ms: 60_000, propose: false, ...(entry ? {entry} : {})})
  expect(r!.refusals).toEqual([])
  return Object.fromEntries(r!.laws.map(l => [l.name, l]))
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
  expect(v['the balances sum to the supply']!.verdict).toBe('proven')
  expect(v['transfer never mints']!.verdict).toBe('proven')
}, 600_000)

t('the DAO\'s shape: broken by a re-entrant run, replayed on the code; cleared first, proven', async () => {
  const bad = (await verdicts(file('VaultBad', VAULT(false))))['the vault holds what it owes']!
  expect(bad.verdict).toBe('broken')
  expect(bad.replayed).toMatch(/replayed on the code.*calls made from inside another/)
  expect(bad.run!.some(s => s.includes('withdraw$resume'))).toBe(true)
  expect((await verdicts(file('VaultGood', VAULT(true))))['the vault holds what it owes']!.verdict).toBe('proven')
}, 900_000)

t('a lock held across the call: re-entering withdraw reverts, the law proven', async () => {
  const v = await verdicts(file('Guarded', `
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
}`))
  expect(v['the vault holds what it owes']!.verdict).not.toBe('broken')
}, 900_000)

t('a wrap past 2^256: unchecked, a counter below its start is reached; checked, never', async () => {
  const src = (unchecked: boolean) => `
/// gdp: law never below the start: count >= 0 and count <= 100
contract Counter {
    uint256 public count;
    function down() external { ${unchecked ? 'unchecked { count -= 1; }' : 'count -= 1;'} }
    function up() external { require(count < 100); count += 1; }
}`
  expect((await verdicts(file('Wraps', src(true))))['never below the start']!.verdict).toBe('broken')
  expect((await verdicts(file('Reverts', src(false))))['never below the start']!.verdict).toBe('proven')
}, 900_000)

t('refused, each where it is with why', () => {
  const why = (name: string, body: string) => { const x = extractSolidity(file(name, body)); expect(x.ok).toBe(false); return x.refusals[0]!.what }
  expect(why('Loop', 'contract Loop { uint256 x; function f(uint256 n) external { for (uint256 i; i < n; i++) x += 1; } }')).toMatch(/a loop/)
  expect(why('Order', 'contract Order { address a; function f(address b) external { require(a < b); a = b; } }')).toMatch(/addresses ordered/)
  expect(why('Other', 'interface T { function g() external; }\ncontract Other { uint256 x; function f(address t) external { T(t).g(); x = 1; } }')).toMatch(/another contract/)
  expect(why('Big', 'contract Big { uint256 x; function f() external { x = 1e18; } }')).toMatch(/past the rule's 2\^53/)
}, 300_000)
