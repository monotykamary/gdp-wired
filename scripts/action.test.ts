import {expect, setDefaultTimeout, test} from 'bun:test'
import {chmodSync, mkdtempSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {spawnSync} from 'node:child_process'

setDefaultTimeout(120_000)
const root = new URL('../', import.meta.url).pathname
const action = Bun.YAML.parse(readFileSync(join(root, 'action.yml'), 'utf8')) as {
  inputs: Record<string, {default?: string, required?: boolean}>,
  runs: {steps: {if?: string, shell?: string, run?: string}[]},
}
const commands = action.runs.steps.filter(s => s.run)
const command = (security = action.inputs.security!.default!) => {
  const matches = commands.filter(s => s.if === (security === 'true' ? "inputs.security == 'true'" : "inputs.security != 'true'"))
  expect(matches).toHaveLength(1)
  return matches[0]!.run!
}
const mock = (security?: string) => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-action-command-'))
  try {
    const npx = join(dir, 'npx')
    writeFileSync(npx, '#!/bin/sh\nprintf "%s\\n" "$@"\nexit "${MOCK_EXIT:-0}"\n')
    chmodSync(npx, 0o755)
    const run = command(security).replaceAll('${{ inputs.version }}', '0.46.0').replaceAll('${{ inputs.paths }}', 'one.ts two.py').replaceAll('${{ inputs.args }}', '--entry Counter --no-propose')
    const p = spawnSync('bash', ['-c', run], {env: {...process.env, PATH: `${dir}:${process.env.PATH}`}, encoding: 'utf8'})
    expect(p.status).toBe(0)
    return p.stdout.trim().split('\n')
  } finally { rmSync(dir, {recursive: true, force: true}) }
}

test('security input is opt-in and the default Action command is unchanged', () => {
  expect(action.inputs.security).toMatchObject({required: false, default: 'false'})
  expect(command()).toBe('npx -y -p typescript@5.9.3 -p gdp-wired@${{ inputs.version }} gdp-wired check ${{ inputs.paths }} ${{ inputs.args }}')
  expect(mock()).toEqual(['-y', '-p', 'typescript@5.9.3', '-p', 'gdp-wired@0.46.0', 'gdp-wired', 'check', 'one.ts', 'two.py', '--entry', 'Counter', '--no-propose'])
})
test('security true appends the CLI flag without replacing paths or args', () => {
  expect(mock('true')).toEqual([...mock('false'), '--security'])
})
test('the workflow exercises the local Action against an isolated fixture repository', () => {
  const workflow = Bun.YAML.parse(readFileSync(join(root, '.github/workflows/security-action.yml'), 'utf8')) as {
    jobs: {'fixture-repository': {steps: {uses?: string, with?: {path?: string, security?: boolean}, run?: string, 'continue-on-error'?: boolean}[]}},
  }
  const steps = workflow.jobs['fixture-repository'].steps
  expect(steps.find(s => s.uses === 'actions/checkout@v5')!.with!.path).toBe('source')
  const actions = steps.filter(s => s.uses === './source')
  expect(actions).toHaveLength(3)
  expect(actions.map(s => s.with?.security ?? false)).toEqual([false, true, true])
  expect(actions[2]!['continue-on-error']).toBe(true)
  expect(steps.some(s => s.run?.includes('git -C "$fixture" init'))).toBe(true)
})

const cli = (file: string, security: boolean) => spawnSync(process.execPath,
  [join(root, 'core/cli.ts'), 'check', join(root, '.github/fixtures/security-action', file), '--no-propose', '--ms', '2000', ...(security ? ['--security'] : [])],
  {cwd: root, encoding: 'utf8', timeout: 90_000, maxBuffer: 4 << 20})
test('candidate-only Action fixture prints review-required policies and exits zero', () => {
  const r = cli('candidate.ts', true)
  expect(r.status).toBe(0)
  expect(r.stdout).toContain('security candidates (NOT accepted policy')
  expect(r.stdout).toContain('Candidates do not affect the exit code')
  expect(r.stdout).toContain('broken')
})
test('default Action fixture does not print security candidates', () => {
  const r = cli('candidate.ts', false)
  expect(r.status).toBe(0)
  expect(r.stdout).not.toContain('security candidates')
})
test('a broken stated law still exits one with and without security mode', () => {
  for (const security of [false, true]) {
    const r = cli('stated-broken.ts', security)
    expect(r.status).toBe(1)
    expect(r.stdout).toContain('laws stated in the code')
    expect(r.stdout).toContain('broken')
  }
})
