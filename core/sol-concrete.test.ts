import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, readFileSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {check, checkTarget} from './cli.ts'
import {extractSolidity, readSolidity} from './extract-sol.ts'

const has = (cmd: string) => { try { execFileSync(cmd, ['--version'], {stdio: 'ignore'}); return true } catch { return false } }
const t = has('solc') && has('anvil') ? test : test.skip
function fixture(body: string, more: Record<string, string> = {}) {
  const root = mkdtempSync(`${tmpdir()}/gdp-sol-concrete-`), file = `${root}/Target.sol`
  const write = (name: string, src: string) => writeFileSync(`${root}/${name}`, `// SPDX-License-Identifier: MIT\npragma solidity ^0.8.20;\n${src}\n`)
  write('Target.sol', body)
  for (const [name, src] of Object.entries(more)) write(name, src)
  return {file, root}
}
const checks = {runs: 6, depth: 5, states: 6}

t('an ordinary concrete entry stays ordinary', () => {
  const {file, root} = fixture('contract Target { uint256 public count; function add(uint256 n) external { count += n; } }')
  const r = readSolidity(file, {root, entry: 'Target'})
  expect(r.c.harness).toBeUndefined()
  expect(r.meta.contract).toBe('Target')
})

t('an abstract class becomes only a constructor-forwarding subclass, checked on its bytecode', () => {
  const {file, root} = fixture('abstract contract Target { uint256 public count; constructor(uint256 start) { count = start; } function add(uint256 n) external { count += n; } }')
  const original = readFileSync(file, 'utf8')
  const x = extractSolidity(file, {root, entry: 'Target', check: checks})
  expect(x.refusals).toEqual([])
  expect(x.ok).toBe(true)
  expect(x.harness?.kind).toBe('constructor')
  expect(x.harness?.generatedSource).toContain('constructor(uint256 __gdp_arg0) Target(__gdp_arg0) {}')
  expect(x.harness?.generatedSource).not.toContain('function ')
  expect(x.harness?.overrides).toEqual([])
  expect(x.notes.join('\n')).toContain('not every possible subclass')
  expect(readFileSync(file, 'utf8')).toBe(original)
}, 180_000)

t('a missing indirect base constructor is forwarded without replacing its body', () => {
  const {file, root} = fixture('contract Base { uint256 public count; constructor(uint256 start) { count = start; } function add(uint256 n) external { count += n; } } abstract contract Target is Base {}')
  const x = extractSolidity(file, {root, entry: 'Target', check: checks})
  expect(x.refusals).toEqual([])
  expect(x.harness?.generatedSource).toContain('Base(__gdp_arg0)')
}, 180_000)

t('constructor forwarding preserves shadowed parameters and base-to-derived execution', () => {
  const {file, root} = fixture('contract Base { uint256 public a; uint256 public afterBase; constructor(uint256 n) { a = n; n += 1; afterBase = n; } } abstract contract Target is Base { uint256 public b; constructor(uint256 n) Base(n + 1) { b = n; } function set(uint256 n) external { b = n; } }')
  const x = extractSolidity(file, {root, entry: 'Target', check: checks})
  expect(x.refusals).toEqual([])
  expect(x.harness?.generatedSource).toContain('Target(__gdp_arg0)')
}, 180_000)

t('constructor type spans use Solidity UTF-8 byte offsets', () => {
  const {file, root} = fixture('// café 日本語\nabstract contract Target { uint256 public count; constructor(uint256 n) { count = n; } function set(uint256 n) external { count = n; } }')
  const r = readSolidity(file, {root, entry: 'Target'})
  expect(r.c.harness?.generatedSource).toContain('constructor(uint256 __gdp_arg0)')
})

t('abstract methods are not invented', () => {
  const {file, root} = fixture('abstract contract Target { function choose(uint256 n) internal virtual returns (uint256); function add(uint256 n) external { choose(n); } }')
  const x = extractSolidity(file, {root, entry: 'Target'})
  expect(x.ok).toBe(false)
  expect(x.refusals[0]?.what).toContain('cannot invent their bodies')
})

t('the repository mock is preferred and its hook implementations are disclosed', () => {
  const {file, root} = fixture('abstract contract Target { uint256 public count; function choose(uint256 n) internal virtual returns (uint256); function set(uint256 n) external { count = choose(n); } }', {
    'Mock.sol': 'import "./Target.sol"; contract TargetMock is Target { function choose(uint256 n) internal override returns (uint256) { return n; } }',
  })
  const original = readFileSync(file, 'utf8')
  const x = extractSolidity(file, {root, entry: 'Target', check: checks})
  expect(x.refusals).toEqual([])
  expect(x.harness?.kind).toBe('repository')
  expect(x.harness?.entry).toBe('TargetMock')
  expect(x.harness?.overrides.join('\n')).toContain('TargetMock.choose(uint256)')
  expect(x.harness?.generatedSource).toBeUndefined()
  expect(readFileSync(file, 'utf8')).toBe(original)
}, 180_000)

t('an unrelated explicit harness is rejected, even with a same-named base', () => {
  const {file, root} = fixture('abstract contract Target { uint256 public count; function set(uint256 n) external { count = n; } }', {
    'Wrong.sol': 'contract Target { uint256 public count; } contract Wrong is Target {}',
  })
  const x = extractSolidity(file, {root, entry: 'Target', harness: {file: 'Wrong.sol', entry: 'Wrong'}})
  expect(x.ok).toBe(false)
  expect(x.refusals[0]?.what).toContain('expected one concrete subclass')
})

t('several unranked repository harnesses require an explicit selection', () => {
  const {file, root} = fixture('abstract contract Target { uint256 public count; function set(uint256 n) external { count = n; } }', {
    'Mock.sol': 'import "./Target.sol"; contract First is Target {} contract Second is Target {}',
  })
  const refused = extractSolidity(file, {root, entry: 'Target'})
  expect(refused.ok).toBe(false)
  expect(refused.refusals[0]?.what).toContain('several concrete repository harnesses')
  const chosen = readSolidity(file, {root, entry: 'Target', harness: {file: 'Mock.sol', entry: 'Second'}})
  expect(chosen.c.harness?.entry).toBe('Second')
})

t('a later lowering refusal retains the chosen harness and its assumptions', () => {
  const {file, root} = fixture('abstract contract Target { uint256 public count; function set(uint256 n) external { for (uint256 i; i < n; ++i) count += i; } }', {
    'Mock.sol': 'import "./Target.sol"; contract TargetMock is Target {}',
  })
  const x = extractSolidity(file, {root, entry: 'Target'})
  expect(x.ok).toBe(false)
  expect(x.refusals[0]?.what).toContain('a loop')
  expect(x.harness?.kind).toBe('repository')
  expect(x.notes.join('\n')).toContain('harness scope')
})

t('an internal pure library is called through an unchanged forwarding body', () => {
  const {file, root} = fixture('library Target { function next(uint256 n) internal pure returns (uint256) { return n + 1; } }')
  const original = readFileSync(file, 'utf8')
  const x = extractSolidity(file, {root, entry: 'Target', check: checks})
  expect(x.refusals).toEqual([])
  expect(x.ok).toBe(true)
  expect(x.harness?.kind).toBe('library')
  expect(x.harness?.generatedSource).toContain('return Target.next(__gdp_arg0);')
  expect(x.harness?.generatedSource).not.toContain('n + 1')
  expect(x.harness?.addedMethods).toEqual(['next(uint256)'])
  expect(readFileSync(file, 'utf8')).toBe(original)
}, 180_000)

t('linked libraries and storage context are not silently replaced', () => {
  const pub = fixture('library Target { function next(uint256 n) public pure returns (uint256) { return n + 1; } }')
  expect(extractSolidity(pub.file, {root: pub.root, entry: 'Target'}).refusals[0]?.what).toContain('deployed, linked library')
  const storage = fixture('library Target { struct S { uint256 count; } function next(S storage s) internal { s.count++; } }')
  expect(extractSolidity(storage.file, {root: storage.root, entry: 'Target'}).refusals[0]?.what).toContain('storage parameter')
})

t('an explicitly selected view is exposed; an unrelated unsupported method is not selected', () => {
  const {file, root} = fixture('contract Target { uint256 public count; function current() external view returns (uint256) { return count; } function unsupported() external { for (;;) count++; } }')
  const r = readSolidity(file, {root, entry: 'Target', methods: ['current']})
  expect(Object.keys(r.meta.entries)).toEqual(['current'])
})

t('a repository override uses its most-derived body, not the inherited implementation', () => {
  const {file, root} = fixture('abstract contract Target { uint256 public count; function set(uint256 n) public virtual { count = n; } }', {
    'Mock.sol': 'import "./Target.sol"; contract TargetMock is Target { function set(uint256 n) public override { count = n + 1; } }',
  })
  const x = extractSolidity(file, {root, entry: 'Target', check: checks})
  expect(x.refusals).toEqual([])
  expect(x.harness?.overrides.join('\n')).toContain('TargetMock.set(uint256)')
}, 180_000)

t('CLI configuration passes an explicitly selected harness to the Solidity frontend', async () => {
  const {file, root} = fixture('abstract contract Target { uint256 public count; function set(uint256 n) external { count = n; } }', {
    'Mock.sol': 'import "./Target.sol"; contract First is Target {} contract Second is Target {}',
  })
  writeFileSync(`${root}/gdp.toml`, '[rules.Target]\nentry = "Target"\n[rules.Target.harness]\nfile = "Mock.sol"\nentry = "Second"\n')
  const result = await check([file], {root, ms: 1000, propose: false, check: checks})
  expect(result.rules).toHaveLength(1)
  expect(result.rules[0]!.refusals).toEqual([])
  expect(result.rules[0]!.notes.join('\n')).toContain('Mock.sol:Second')
}, 180_000)

t('invalid harness configuration does not silently fall back to auto', () => {
  const {file, root} = fixture('abstract contract Target { uint256 public count; function set(uint256 n) external { count = n; } }')
  for (const harness of ['false', {}, {file: 7}, {file: 'Mock.sol', entry: 3}]) {
    const x = extractSolidity(file, {root, entry: 'Target', harness: harness as never})
    expect(x.ok).toBe(false)
    expect(x.refusals[0]?.what).toContain('harness must be')
  }
})

t('harnessing can be disabled explicitly', () => {
  const {file, root} = fixture('abstract contract Target { uint256 public count; function add(uint256 n) external { count += n; } }')
  const x = extractSolidity(file, {root, entry: 'Target', harness: false})
  expect(x.ok).toBe(false)
  expect(x.refusals[0]?.what).toContain('an abstract contract')
  expect(x.harness).toBeUndefined()
})

t('a vulnerable inherited body is refuted and replayed; the fixed original is not refuted', async () => {
  const verdict = async (fixed: boolean) => {
    const {file, root} = fixture(`/// gdp: law spending stays within its cap: spent <= 10\nabstract contract Target { uint256 public spent; function spend(uint256 n) external { if (${fixed ? 'n <= 10 - spent' : 'spent < 10'}) spent += n; } }`)
    const [r] = await checkTarget({lang: 'solidity', at: file, files: [file]}, {root, entry: 'Target', propose: false, ms: 60_000, check: checks})
    expect(r!.refusals).toEqual([])
    return r!.laws.find(l => l.name === 'spending stays within its cap')!
  }
  const bad = await verdict(false)
  expect(bad.verdict).toBe('broken')
  expect(bad.replayed).toContain('replayed on the code')
  expect((await verdict(true)).verdict).toBe('proven')
}, 300_000)
