// The access audit on WebGPU: every (user, project) pair of an org under two policies, against the same spec compiled
// to plain JavaScript in this page. Every count of every user is compared, and every per-project code of the window.
import {emitBitLoopWgsl} from '../../vendor/handwired/src/json-search/bit-emit.ts'
import {emitLoopWgsl} from '../../vendor/handwired/src/json-search/loop-emit.ts'
import {createDocumentStore, createProgramRunner, requestBatchDevice} from '../../vendor/handwired/src/json-search/gpu/host.ts'
import {createLoopRunner} from '../../vendor/handwired/src/json-search/loop-program.ts'
import {compileEmptyPipeline, createReporter, round, sample, summary} from '../../vendor/handwired/lab/json-search/gpu/measure.ts'
import {buildAudit, userCells, writeUserCells} from '../audit/circuit.ts'
import {type AuditCounts, compileJsAudit, sparseJsAudit} from '../audit/js-audit.ts'
import {evalBool, generateOrg} from '../audit/model.ts'
import {atomNames, atoms, policies, truthTable} from '../audit/spec.ts'

export type PageConfig = {
  counts: number[], projects: number, teams: number, domains: number, salt: number, jsLimit: number,
  warmupMs: number, sampleMs: number, minimumSamples: number, maximumSamples: number, cpuWarmupMs: number, cpuSampleMs: number, cpuSamples: number,
}

const {report, post, log} = createReporter()
const config = await (await fetch('/config')).json() as PageConfig
report['config'] = config
const results: Record<string, unknown>[] = []
report['results'] = results

try {
  const maxUsers = Math.max(...config.counts)
  const {projects, teams, domains} = config
  const org = generateOrg({users: maxUsers, teams, projects, domains})
  const tableA = truthTable(policies.canViewProtection)
  const tableB = truthTable(policies.canViewProtectionProposed)
  const tableSet = truthTable(policies.canSetProtection)
  const built = buildAudit({projects, teams, domains})
  const shared = new Float32Array(built.loop.sharedValues)
  built.writeShared(shared, org, tableA, tableB)
  // A policy edit: canSetProtection in place of the proposal, which uploads 1,367 shared cells and no shader.
  const editedShared = new Float32Array(shared)
  built.writeShared(editedShared, org, tableA, tableSet)
  const cells = writeUserCells(org)
  const windowUsers = 64

  const granted = await requestBatchDevice(Math.max(cells.byteLength, maxUsers * 16, windowUsers * projects * 4))
  const {device} = granted
  report['adapter'] = granted.adapterInfo
  report['emptyPipelineMs'] = round(await compileEmptyPipeline(device, config.salt))
  const store = await createDocumentStore(device, userCells, maxUsers)
  store.write(cells, maxUsers)

  const shaders = {'bit-emit': emitBitLoopWgsl(built.loop), 'loop-emit': emitLoopWgsl(built.loop)}
  const runners = {} as Record<keyof typeof shaders, Awaited<ReturnType<typeof createProgramRunner>>>
  for (const [writer, shader] of Object.entries(shaders) as [keyof typeof shaders, (typeof shaders)[keyof typeof shaders]][]) {
    runners[writer] = await createProgramRunner(device, shader, shared, store, config.salt, {windowCapacity: windowUsers})
    log(`${writer}: ${shader.statementCount} statements, compiled in ${round(runners[writer].compileMs)} ms`)
  }

  const jsAudit = compileJsAudit()
  const newCounts = (users: number): AuditCounts => ({allowedA: new Float64Array(users), allowedB: new Float64Array(users), gained: new Float64Array(users), lost: new Float64Array(users)})
  const keys = ['allowedA', 'allowedB', 'gained', 'lost'] as const

  // The circuit itself on the CPU, as generated JavaScript, per user.
  const cpuRunner = createLoopRunner(built.loop, 'generated')
  cpuRunner.setShared(shared)
  const cpuOutputs = [new Float32Array(4 * 200), new Float32Array(projects)]
  const cpuStarted = performance.now()
  for (let user = 0; user < 200; user++) cpuRunner.run([cells], user, cpuOutputs, user, -1)
  report['circuitOnCpuMicrosecondsPerUser'] = round((performance.now() - cpuStarted) * 1000 / 200)

  for (const count of config.counts) {
    const entry: Record<string, unknown> = {users: count, pairs: count * projects}
    results.push(entry)
    // The reference for this count, timed when it's small enough to time.
    const expected = newCounts(count)
    const jsStarted = performance.now()
    jsAudit(org, tableA, tableB, 0, count, expected)
    const jsMs = performance.now() - jsStarted
    if (count <= config.jsLimit) {
      const times: number[] = []
      for (let index = 0; index < config.cpuSamples; index++) {
        const started = performance.now()
        jsAudit(org, tableA, tableB, 0, count, newCounts(count))
        times.push(performance.now() - started)
      }
      entry['jsMs'] = summary(times)
    } else {
      entry['jsMsOnce'] = round(jsMs)
    }
    {
      const sparse = newCounts(count)
      const times: number[] = []
      for (let index = 0; index < config.cpuSamples; index++) {
        const started = performance.now()
        sparseJsAudit(org, tableA, tableB, 0, count, sparse)
        times.push(performance.now() - started)
      }
      let sparseMismatches = 0
      for (let user = 0; user < count; user++) for (const key of keys) if (sparse[key][user] !== expected[key][user]) sparseMismatches++
      entry['sparseJs'] = {ms: summary(times), mismatches: sparseMismatches}
      log(`${count} users: sparse JS ${JSON.stringify(entry['sparseJs'])}`)
    }
    const window = {firstDocument: 0, documentCount: Math.min(count, windowUsers)}
    for (const writer of Object.keys(runners) as (keyof typeof runners)[]) {
      const runner = runners[writer]
      runner.writeShared(shared)
      const evaluateOnce = () => runner.evaluate({count, window, readbacks: [{group: 0, firstDocument: 0, documentCount: count}]})
      const first = await evaluateOnce()
      let mismatches = 0
      for (let user = 0; user < count; user++) {
        keys.forEach((key, column) => {
          if (first.outputs[0]![user * 4 + column] !== expected[key][user]) mismatches++
        })
      }
      const codes = await runner.read({group: 1, firstDocument: 0, documentCount: window.documentCount})
      let codeMismatches = 0
      for (let user = 0; user < window.documentCount; user++) {
        for (let project = 0; project < projects; project++) {
          const index = atomNames.reduce((sum, name, bit) => sum + (evalBool(org, atoms[name].expr, user, project) ? 1 << bit : 0), 0)
          if (codes[user * projects + project] !== tableA[index]! + 2 * tableB[index]!) codeMismatches++
        }
      }
      const samples = await sample(config, evaluateOnce)
      const edit = await sample(config, () => runner.evaluate({count, shared: editedShared, readbacks: [{group: 0, firstDocument: 0, documentCount: count}]}))
      runner.writeShared(shared)
      entry[writer] = {
        mismatches, codeMismatches,
        backToBackMs: summary(samples.map(s => s.totalMs)),
        passMs: runner.hasTimestamps ? summary((await sample({...config, minimumSamples: 5, maximumSamples: 20}, () => runner.evaluate({count, readbacks: [], timestamps: true}))).map(s => s.passMs)) : undefined,
        policyEditMs: summary(edit.map(s => s.totalMs)),
      }
      log(`${count} users × ${projects} projects, ${writer}: ${JSON.stringify(entry[writer])}`)
    }
    log(`${count} users: JS audit ${JSON.stringify(entry['jsMs'] ?? entry['jsMsOnce'])} ms`)
    await post(false)
  }
} catch (error) {
  report['error'] = String(error instanceof Error ? error.stack : error)
  log(`error: ${String(error)}`)
}
await post(true)
