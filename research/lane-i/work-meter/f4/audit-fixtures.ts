import {strict as assert} from 'node:assert'
import {auditLog, auditPairs, patch, sha, source} from './audit.ts'
const raw = Object.fromEntries(['fm','fcells','plainRows','values','copies','edges','scan','pivotRows','unitRows','unfoldRows','goalNodes','translateRows','tableCells','checkSteps','astNodes','evals','cubeTests','ticks','cdclNodes','epr'].map(key => [key, 1]))
const make = (id: string, cpu: string, mutate: (row: any) => any = row => row) => {
  const tuple = {id, work: 15000000, result: {proven: false, checked: false, stuck: 'unknown'}, raw}
  const fingerprint = sha(JSON.stringify(tuple)), base = {...tuple, source, cpu, arch: 'x64', runtime: 'fixture', fingerprint, phaseReconciliation: true, affinity: '0', seedPolicy: 'production defaults, no override', unitModel: 'legacy fixed allowance for raw determinism only; not calibrated W'}
  const sections = [1,2].map(repetition => { const stdout = 'RAW_CENSUS_RECORD ' + JSON.stringify(mutate({...base, repetition})) + '\n'; return 'RAW_CENSUS_PROCESS ' + JSON.stringify({id, repetition, exit: 0, signal: null, error: '', stdoutSha256: sha(stdout)}) + '\n' + stdout + '\n' })
  return 'COMPOSITION_VERIFIED ' + JSON.stringify({mode: 'canonical', patchSha256: patch}) + '\n' + sections.join('') + 'RAW_CENSUS_PAIR ' + JSON.stringify({...base, passed: true, repeats: 2}) + '\n'
}
const ids = ['consensus','consensus_epr','mldr']
const good = make('mldr', 'cpu-a')
assert.equal(auditLog(good, 'mldr').passed, true)
assert.throws(() => auditLog(good.replace(patch, 'wrong'), 'mldr'))
assert.throws(() => auditLog(good.replace('"exit":0', '"exit":1'), 'mldr'))
assert.throws(() => auditLog(good.replace('"fm":1', '"fm":2'), 'mldr'))
assert.throws(() => auditLog(good.replace('"repetition":2', '"repetition":1'), 'mldr'))
for (const mutate of [
  (row: any) => ({...row, phaseReconciliation: false}),
  (row: any) => ({...row, source: 'wrong'}),
  (row: any) => ({...row, raw: {...row.raw, fm: -1}}),
  (row: any) => ({...row, seedPolicy: 'test override'}),
]) assert.throws(() => auditLog(make('mldr', 'cpu-a', mutate), 'mldr'))
const pairs = ids.flatMap(id => ['cpu-a','cpu-b'].map(cpu => auditLog(make(id, cpu), id)))
assert.equal(auditPairs(pairs).crossCpuProtocols.length, 3)
assert.throws(() => auditPairs(pairs.slice(1)))
assert.throws(() => auditPairs(pairs.map((row, index) => index ? row : {...row, fingerprint: 'wrong'})))
const sameCpu = ids.flatMap(id => [1,2].map(() => auditLog(make(id, 'same-cpu'), id)))
assert.equal(auditPairs(sameCpu).crossCpuProtocols.length, 0)
console.log('RAW_CENSUS_AUDITOR_FIXTURES ' + JSON.stringify({passed: true, corruptionsRejected: 10, cpuAliasNotOverclaimed: true, syntheticOnly: true}))
