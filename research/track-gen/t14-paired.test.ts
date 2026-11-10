import {expect, test} from 'bun:test'
import {chmodSync, mkdirSync, mkdtempSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
const script = new URL('./t14-paired.sh', import.meta.url).pathname
function paired(mode: string, failedSide: string, repeat: number, code = 7) {
  const root = mkdtempSync(join(tmpdir(), 'gdp-pair-exit-'))
  try {
    for (const dir of ['bin', 'baselines', 'empty', 'vendor', 'research/track-gen']) mkdirSync(join(root, dir), {recursive: true})
    for (const name of ['t13-generation.ts', 't14-measure.ts']) writeFileSync(join(root, 'research/track-gen', name), '// fixture only\n')
    const bun = join(root, 'bin/bun')
    writeFileSync(bun, `#!/usr/bin/env bash
set -eu
if [[ "\${1:-}" == install ]]; then exit 0; fi
if [[ "$*" == *t13-compare.ts* ]]; then exit 0; fi
side=baseline
[[ "$PWD" == "$PAIR_FAKE_ROOT" ]] && side=candidate
# Even a complete-looking payload before a failure must not count as success.
printf 'fake payload from %s\\n' "$side"
if [[ "$side" == "$PAIR_FAIL_SIDE" ]]; then exit "$PAIR_FAIL_CODE"; fi
exit 0
`)
    chmodSync(bun, 0o755)
    const tar = Bun.spawnSync(['tar', '-cf', join(root, 'baselines/main.tar'), '-C', join(root, 'empty'), '.'])
    if (tar.exitCode !== 0) throw Error('fixture archive failed')
    const run = Bun.spawnSync(['bash', script, mode, 'fixture', String(repeat), 'main'], {
      cwd: root, env: {...process.env, PATH: `${join(root, 'bin')}:${process.env.PATH ?? ''}`, PAIR_FAKE_ROOT: root, PAIR_FAIL_SIDE: failedSide, PAIR_FAIL_CODE: String(code)}, stdout: 'pipe', stderr: 'pipe',
    })
    return {code: run.exitCode, output: new TextDecoder().decode(run.stdout)}
  } finally { rmSync(root, {recursive: true, force: true}) }
}
for (const mode of ['generation', 'original']) {
  test(`${mode}: both successful sides return success`, () => {
    const run = paired(mode, 'none', 1)
    expect(run.code).toBe(0)
    expect(run.output).toContain('PAIR end side=candidate exit=0')
    expect(run.output).toContain('PAIR end side=baseline exit=0')
  })
  for (const side of ['candidate', 'baseline']) for (const repeat of [1, 2]) {
    test(`${mode}: ${side} failure propagates with repeat ${repeat}`, () => {
      const run = paired(mode, side, repeat)
      expect(run.code).not.toBe(0)
      expect(run.output).toContain(`PAIR end side=${side} exit=7`)
      expect(run.output.match(/^PAIR end side=/gm)).toHaveLength(2)
    })
  }
}
test('a killed original side cannot become pair success', () => {
  const run = paired('original', 'candidate', 1, 137)
  expect(run.code).not.toBe(0)
  expect(run.output).toContain('PAIR end side=candidate exit=137')
  expect(run.output).toContain('PAIR end side=baseline exit=0')
})
