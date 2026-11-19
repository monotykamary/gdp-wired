// Untrusted Lean 4.34.0 certificate emitter for checked accelerated refutations.
// Emits a standalone proof of `∃ ρ M, SReach source ρ M ∧ ¬ law.Holds ρ M`
// against the unmodified SMachine, MLaw, Sets.lean, Kernel.lean, and AccelRefute.lean
// with zero new axioms and zero proof search during replay.
import assert from 'node:assert/strict'
import {type Law, type Machine, interpret, isArithmetic, x} from '../core/machine.ts'
import {type AcceleratedRun, type ClosedFormVar, checkAcceleratedRun} from '../core/accel-refute.ts'
import {encode, machineLit} from './emit.ts'
import {exactNat, leanTerms} from './lean-terms.ts'

const list = (xs: string[]) => `[${xs.join(', ')}]`

function envDef(name: string, entries: [number, string][], fallback = '0'): string {
  const body = entries.reduceRight((acc, [idx, expr]) => `if v = ${idx} then ${expr} else ${acc}`, fallback)
  return `def ${name} (v : Nat) : Nat := ${body}`
}

function phiDef(name: string, entries: [number, ClosedFormVar][], p0Name: string): string {
  const expr = ({base, delta}: ClosedFormVar) => {
    if (delta === 0) return exactNat(base)
    if (delta > 0) return base === 0 ? (delta === 1 ? 'j' : `${exactNat(delta)} * j`) : `${exactNat(base)} + ${delta === 1 ? 'j' : `${exactNat(delta)} * j`}`
    return `${exactNat(base)} - ${-delta === 1 ? 'j' : `${exactNat(-delta)} * j`}`
  }
  const body = entries.reduceRight((acc, [idx, cf]) => `if v = ${idx} then ${expr(cf)} else ${acc}`, `${p0Name} v`)
  return `def ${name} (j : Nat) (v : Nat) : Nat := ${body}`
}

function phiTermLean(jIdx: number, {base, delta}: ClosedFormVar, offset: 0 | 1): string {
  const c = base + offset * delta
  if (delta === 0) return `.const ${exactNat(c)}`
  if (delta > 0) {
    const mul = delta === 1 ? `.var ${jIdx}` : `.mul ${exactNat(delta)} (.var ${jIdx})`
    return c === 0 ? mul : `.add (.const ${exactNat(c)}) (${mul})`
  }
  const dec = -delta
  const mul = dec === 1 ? `.var ${jIdx}` : `.mul ${exactNat(dec)} (.var ${jIdx})`
  return `.sub (.const ${exactNat(c)}) (${mul})`
}

export function acceleratedRefutationToLean(id: string, m: Machine, laws: Law[], acc: AcceleratedRun): string {
  assert(checkAcceleratedRun(m, laws, acc), `${id}: accelerated run failed TypeScript kernel verification`)
  const target = laws.find(l => l.name === acc.law)
  assert(target, `${id}: broken law ${acc.law} not found`)
  assert(!target.forall && !target.keys?.length, `${id}: expected plain safety law`)
  const jVars = [...new Set(acc.segments.flatMap(s => (s.kind === 'repeat' ? [s.jVar] : [])))]
  const flags = Object.keys(m.step.flags ?? {})
  const factKeys = [...new Set((m.facts ?? []).flatMap(f => [f.forall, ...(f.keys ?? [])].filter((k): k is string => !!k)))]
  const vars = [...new Set([
    ...m.params, ...m.inputs, ...Object.keys(m.state),
    ...flags.map(f => `?${f}`), ...factKeys, ...jVars,
  ])]
  const maps = [...new Set([...Object.keys(m.maps ?? {}), ...Object.keys(m.fns ?? {})])]
  const ix = (nm: string) => { const j = vars.indexOf(nm); assert(j >= 0, `missing var ${nm}`); return j }
  const mx = (nm: string) => { const j = maps.indexOf(nm); assert(j >= 0, `missing map ${nm}`); return j }
  const t = leanTerms(vars, maps, id)
  const stateKeys = Object.keys(m.state)
  const stateIndices = stateKeys.map(ix)
  const stateAndParams = [...m.params.map(ix), ...stateIndices]
  const runtimeVars = [...stateAndParams, ...m.inputs.map(ix), ...flags.map(f => ix(`?${f}`))]
  const emitCases = (indent: string, indices: number[], at: (idx: number) => string[], otherwise: (ne: string[]) => string[]) => {
    const ne: string[] = []
    let pad = indent
    for (const idx of indices) {
      const h = `hv${idx}`
      const [head, ...tail] = at(idx)
      lines.push(`${pad}by_cases ${h} : v = ${idx}`, `${pad}· subst v`)
      for (const line of [head!, ...tail]) lines.push(`${pad}  ${line}`)
      lines.push(`${pad}·`)
      ne.push(h, `Ne.symm ${h}`)
      pad += '  '
    }
    for (const line of otherwise(ne)) lines.push(`${pad}${line}`)
  }
  const simp = (defs: string[], ne: string[] = []) => `simp [${[...defs, ...ne].join(', ')}]`

  const lines: string[] = [
    'import Sets',
    'import AccelRefute',
    'open Kern AccelRefute',
    'set_option maxRecDepth 100000',
    'set_option maxHeartbeats 0',
    'set_option linter.unusedSimpArgs false',
    '',
    `-- Checked accelerated refutation for ${id}: ${target.name} (totalSteps = ${acc.totalSteps})`,
    `def ${id}_machine : SMachine := ${machineLit(m, t, ix, mx)}`,
    `def ${id}_law : MLaw := ⟨${t.c(target.holds)}, none⟩`,
    '',
  ]

  // Concrete parameter environment p0
  const paramEntries: [number, string][] = m.params.map(p => [ix(p), exactNat(acc.params[p] ?? 0)])
  lines.push(envDef(`${id}_p0`, paramEntries))

  // Map environment M0 interpreting arithmetic functions div$d / mod$d faithfully
  const mapEntries: [number, string][] = maps.map(mp => {
    if (isArithmetic(mp)) {
      const d = Number(mp.slice(mp.indexOf('$') + 1))
      const op = mp.startsWith('div$') ? '/' : '%'
      return [mx(mp), `(fun k => k ${op} ${d})`]
    }
    return [mx(mp), `(fun _ => ${exactNat(m.maps?.[mp] ?? 0)})`]
  })
  const m0Body = mapEntries.reduceRight((accS, [idx, fn]) => `if mp = ${idx} then ${fn} else ${accS}`, '(fun _ => 0)')
  lines.push(`def ${id}_M0 (mp : Nat) : Nat → Nat := ${m0Body}`)
  lines.push('')

  // Facts proof for M0 (div$d / mod$d Euclidean division identities)
  lines.push(`theorem ${id}_facts : ∀ l ∈ ${id}_machine.facts, l.Holds ${id}_p0 ${id}_M0 := by`)
  lines.push(`  intro l hl`)
  if (!(m.facts ?? []).length) {
    lines.push(`  simp [${id}_machine] at hl`)
  } else {
    lines.push(`  simp only [${id}_machine, List.mem_cons, List.not_mem_nil, or_false] at hl`)
    const nFacts = (m.facts ?? []).length
    const rcasesNames = Array.from({length: nFacts}, () => 'rfl').join(' | ')
    lines.push(`  rcases hl with ${rcasesNames}`)
    for (const f of m.facts ?? []) {
      lines.push(`  · intro a; change evalC (upd ${id}_p0 ${ix(f.forall!)} a) ${id}_M0 (${t.c(f.holds)}) = true`)
      lines.push(`    simp [evalC, evalE, upd, ${id}_M0, ${id}_p0] <;> omega`)
    }
  }
  lines.push('')

  // Initial concrete state env
  const it = interpret(m)
  let curSt = it.init(acc.params)
  const stateEnvDef = (nm: string, st: Record<string, number>) =>
    envDef(nm, [...paramEntries, ...stateKeys.map((sv): [number, string] => [ix(sv), exactNat(st[sv] ?? 0)])])

  lines.push(stateEnvDef(`${id}_st0`, curSt.scalars))
  lines.push(`theorem ${id}_reach0 : ∃ ρ, SReach ${id}_machine ρ ${id}_M0 ∧ AgreeOn ${id}_machine.f.m.inputs ${id}_machine.f.flags ρ ${id}_st0 := by`)
  lines.push(`  apply sreach_start_agree ${id}_machine ${id}_p0 ${id}_M0 ${id}_st0`)
  lines.push(`  · simp [StartMaps, ${id}_machine]`)
  lines.push(`  · decide`)
  lines.push(`  · exact ${id}_facts`)
  lines.push(`  · simp [SMachine.PFacts, ${id}_machine]`)
  lines.push(`  · intro v _ _`)
  emitCases('    ', stateAndParams, () => ['decide +kernel'], ne => [simp([`${id}_machine`, `${id}_st0`, `${id}_p0`, 'applyS', 'assoc', 'lookup'], ne)])
  lines.push('')

  // Emit each concrete or accelerated repeat segment!
  for (let sIdx = 0; sIdx < acc.segments.length; sIdx++) {
    const seg = acc.segments[sIdx]!
    const prevName = `${id}_st${sIdx}`
    const nextName = `${id}_st${sIdx + 1}`
    const reqName = `${id}_req${sIdx}`
    const reqEntries: [number, string][] = m.inputs.map(inp => [ix(inp), exactNat(seg.request[inp] ?? 0)])
    lines.push(envDef(reqName, reqEntries))

    if (seg.kind === 'step') {
      curSt = it.step(acc.params, curSt, seg.request)
      lines.push(stateEnvDef(nextName, curSt.scalars))
      lines.push(`theorem ${id}_reach${sIdx + 1} : ∃ ρ, SReach ${id}_machine ρ ${id}_M0 ∧ AgreeOn ${id}_machine.f.m.inputs ${id}_machine.f.flags ρ ${nextName} := by`)
      lines.push(`  apply sreach_concrete_step ${id}_machine ${id}_M0 ${reqName} ${prevName} ${nextName} rfl rfl rfl rfl (by decide) ${id}_reach${sIdx}`)
      lines.push(`  · decide`)
      lines.push(`  · intro v hvin hvfl`)
      emitCases('    ', runtimeVars, idx => m.inputs.map(ix).includes(idx) ? ['exact False.elim (hvin (by decide))']
        : stateAndParams.includes(idx) ? ['decide +kernel'] : ['exact False.elim (by simpa [flagOf, lookup, ' + `${id}_machine] using hvfl)`],
      ne => [simp([`${id}_machine`, nextName, prevName, reqName, `${id}_p0`, 'applyS', 'decideFlags', 'flagSub', 'assoc', 'lookup', 'withInputs'], ne)])
      lines.push('')
    } else {
      const jIdx = ix(seg.jVar)
      const phiName = `${id}_phi${sIdx}`
      const sigmaName = `${id}_sigma${sIdx}`
      const eqsName = `${id}_eqs${sIdx}`
      const K = exactNat(seg.count)
      const cfEntries: [number, ClosedFormVar][] = stateKeys.map(sv => [ix(sv), seg.closedForm[sv]!])
      lines.push(phiDef(phiName, cfEntries, `${id}_p0`))

      // Substitution σ matching buildRepeatGoals
      const sigmaItems = [
        ...m.params.map(p => `(${ix(p)}, .const ${exactNat(acc.params[p] ?? 0)})`),
        ...m.inputs.map(inp => `(${ix(inp)}, .const ${exactNat(seg.request[inp] ?? 0)})`),
        ...stateKeys.map(sv => `(${ix(sv)}, ${phiTermLean(jIdx, seg.closedForm[sv]!, 0)})`),
      ]
      lines.push(`def ${sigmaName} : List (Nat × E) := ${list(sigmaItems)}`)

      // Step equations list (v, step_v, phiNext_v)
      const eqItems = stateKeys.map(sv => {
        const rhs = m.step.state?.[sv] ?? x(sv)
        return `(${ix(sv)}, ${t.e(rhs)}, ${phiTermLean(jIdx, seg.closedForm[sv]!, 1)})`
      })
      lines.push(`def ${eqsName} : List (Nat × E × E) := ${list(eqItems)}`)

      // Encode allowGoal and stepGoal trees via emit.ts's `encode`!
      const encAllow = encode({name: `${id}_allow${sIdx}`, goal: seg.allowGoal, tree: seg.allowTree}, false, true, vars, maps)
      const encStep = encode({name: `${id}_step${sIdx}`, goal: seg.stepGoal, tree: seg.stepTree}, false, true, vars, maps)
      const allowFacts = seg.allowGoal.hyps.slice(1, -1)
      const stepFacts = seg.stepGoal.hyps.slice(1, -1)

      lines.push(`def ${id}_allowTab${sIdx} : List VDef := ${encAllow.tab}`)
      lines.push(`def ${id}_allowTree${sIdx} : Tree := ${encAllow.tree}`)
      lines.push(`def ${id}_allowFacts${sIdx} : List C := ${list(allowFacts.map(t.c))}`)
      lines.push(`def ${id}_stepTab${sIdx} : List VDef := ${encStep.tab}`)
      lines.push(`def ${id}_stepTree${sIdx} : Tree := ${encStep.tree}`)
      lines.push(`def ${id}_stepFacts${sIdx} : List C := ${list(stepFacts.map(t.c))}`)

      if (m.assume) {
        lines.push(`theorem ${id}_allowCheck${sIdx} : checkGoal ⟨${id}_allowTab${sIdx}, (.lt (.var ${jIdx}) (.const ${K})) :: ${id}_allowFacts${sIdx} ++ [.not (substC ${sigmaName} (inlineC ${id}_machine.f.flags ${id}_machine.f.m.assume))]⟩ ${id}_allowTree${sIdx} = true := by decide +kernel`)
      }
      lines.push(`theorem ${id}_stepCheck${sIdx} : checkGoal ⟨${id}_stepTab${sIdx}, (.lt (.var ${jIdx}) (.const ${K})) :: ${id}_stepFacts${sIdx} ++ [.not (andList (${eqsName}.map fun q => .eq (substE ${sigmaName} (inlineE ${id}_machine.f.flags q.2.1)) q.2.2))]⟩ ${id}_stepTree${sIdx} = true := by decide +kernel`)

      // Substitution equivalence lemma hsub
      lines.push(`theorem ${id}_sub${sIdx} (j v : Nat) (hv : v ≠ ${jIdx}) : applyS ${sigmaName} (upd ${id}_p0 ${jIdx} j) ${id}_M0 v = withInputs ${id}_machine.f.m.inputs (${phiName} j) ${reqName} v := by`)
      const subDefs = [sigmaName, `${id}_machine`, phiName, reqName, `${id}_p0`, 'applyS', 'assoc', 'lookup', 'withInputs', 'evalE', 'upd']
      emitCases('  ', [...stateAndParams, ...m.inputs.map(ix)], () => [simp(subDefs)], ne => [simp(subDefs, [...ne, 'hv'])])

      // Fact soundness lemmas (if any active div$/mod$ facts were instantiated)
      const emitFactProof = (thmName: string, factsName: string, factsList: typeof allowFacts) => {
        lines.push(`theorem ${thmName} (j : Nat) (_hj : j < ${K}) : ∀ c ∈ ${factsName}, evalC (upd ${id}_p0 ${jIdx} j) ${id}_M0 c = true := by`)
        lines.push(`  intro c hc`)
        if (!factsList.length) {
          lines.push(`  simp [${factsName}] at hc`)
        } else {
          lines.push(`  simp only [${factsName}, List.mem_cons, List.not_mem_nil, or_false] at hc`)
          lines.push(`  rcases hc with ${factsList.map(() => 'rfl').join(' | ')}`)
          for (let fi = 0; fi < factsList.length; fi++) {
            lines.push(`  · simp [evalC, evalE, upd, ${id}_M0, ${id}_p0] <;> omega`)
          }
        }
      }
      emitFactProof(`${id}_allowFactsOk${sIdx}`, `${id}_allowFacts${sIdx}`, allowFacts)
      emitFactProof(`${id}_stepFactsOk${sIdx}`, `${id}_stepFacts${sIdx}`, stepFacts)

      // Next concrete state after K repeats
      curSt = {scalars: {...seg.endState}, maps: {}}
      lines.push(stateEnvDef(nextName, curSt.scalars))
      lines.push(`theorem ${id}_reach${sIdx + 1} : ∃ ρ, SReach ${id}_machine ρ ${id}_M0 ∧ AgreeOn ${id}_machine.f.m.inputs ${id}_machine.f.flags ρ ${nextName} := by`)
      lines.push(`  have hrep : ∃ ρ, SReach ${id}_machine ρ ${id}_M0 ∧ AgreeOn ${id}_machine.f.m.inputs ${id}_machine.f.flags ρ (${phiName} ${K}) := by`)
      lines.push(`    apply sreach_repeat_checked ${id}_machine ${id}_M0 ${reqName} ${K} ${phiName} rfl rfl rfl rfl (by decide)`)
      lines.push(`    · obtain ⟨ρ, hr, ha⟩ := ${id}_reach${sIdx}`)
      lines.push(`      refine ⟨ρ, hr, fun v hvin hvfl => (ha v hvin hvfl).trans ?_⟩`)
      emitCases('      ', stateAndParams, () => ['decide +kernel'], ne => [simp([prevName, phiName, `${id}_p0`], ne)])
      if (m.assume) {
        lines.push(`    · exact allow_of_goal ${id}_machine ${id}_M0 ${id}_p0 ${reqName} ${jIdx} ${K} ${phiName} ${sigmaName} ${id}_allowFacts${sIdx} ${id}_allowTab${sIdx} ${id}_allowTree${sIdx} ${id}_allowCheck${sIdx} (by decide) ${id}_allowFactsOk${sIdx} ${id}_sub${sIdx}`)
      } else {
        lines.push(`    · intro _ _; rfl`)
      }
      lines.push(`    · apply step_of_goal ${id}_machine ${id}_M0 ${id}_p0 ${reqName} ${jIdx} ${K} ${phiName} ${sigmaName} ${eqsName} ${id}_stepFacts${sIdx} ${id}_stepTab${sIdx} ${id}_stepTree${sIdx} ${id}_stepCheck${sIdx} (by decide) ${id}_stepFactsOk${sIdx} ${id}_sub${sIdx}`)
      lines.push(`      · intro v e ha`)
      const written = Object.keys(m.step.state ?? {}).map(ix)
      const assocDefs = [`${id}_machine`, 'assoc', 'lookup']
      emitCases('        ', written, idx => {
        const rhs = phiTermLean(jIdx, seg.closedForm[vars[idx]!]!, 1)
        return [`${simp(assocDefs)} at ha`, 'subst e',
          `refine ⟨${rhs}, by simp [${eqsName}], ?_⟩`,
          `intro j hj`, `${simp(['evalE', 'upd', phiName])} <;> omega`]
      }, ne => [`${simp(assocDefs, ne)} at ha`])
      lines.push(`      · intro j hj v hvin hvfl ha`)
      emitCases('        ', stateIndices, idx => written.includes(idx)
        ? [`${simp(assocDefs)} at ha`] : [simp([phiName])], ne => [simp([phiName], ne)])
      lines.push(`  obtain ⟨ρ, hr, ha⟩ := hrep`)
      lines.push(`  refine ⟨ρ, hr, fun v hvin hvfl => (ha v hvin hvfl).trans ?_⟩`)
      emitCases('  ', stateAndParams, () => ['decide +kernel'], ne => [simp([phiName, nextName, `${id}_p0`], ne)])
      lines.push('')
    }
  }

  const finalName = `${id}_st${acc.segments.length}`
  lines.push(`/-- Exact refutation of \`${target.name}\` on the unmodified original machine (k = ${acc.totalSteps} steps). -/`)
  lines.push(`theorem ${id}_refuted : ∃ ρ M, SReach ${id}_machine ρ M ∧ ¬ ${id}_law.Holds ρ M :=`)
  lines.push(`  refutes_of_reached ${id}_machine ${id}_M0 ${id}_law ${finalName} rfl (by decide) ${id}_reach${acc.segments.length} (by decide)`)
  lines.push('')
  lines.push(`#print axioms ${id}_refuted`)
  return lines.join('\n') + '\n'
}
