import {describe, expect, test} from 'bun:test'
import {type E, type Law, type Machine, atMost, get, ite, n, not, plus, same, x} from '../core/machine.ts'
import {bool, choose, forall, nat, no, oneOf, proveRule, record, rule, when, yes} from '../core/dsl.ts'
import {proofOutput, type PublicProofOutput} from '../core/proof-output.ts'
import {type GroupedSumCertificate, checkGroupedSum, groupedSumTheory} from './grouped-sum.ts'
import {type Tree, obligations} from './kernel.ts'
import {grow, proveLaws} from './prove.ts'
import {toLean} from '../lean-kernel/emit.ts'
import {groupedSumToLean} from '../lean-kernel/grouped-sum-export.ts'

const findAgg = (node: PublicProofOutput['proof'] | undefined): Extract<NonNullable<PublicProofOutput['proof']>, {kind: 'aggregate'}> | undefined => {
  if (!node) return undefined
  if (node.kind === 'aggregate') return node
  if (node.kind === 'derived') {
    for (const p of node.parents) {
      const hit = findAgg(p)
      if (hit) return hit
    }
  }
  return undefined
}

function makeDuckDB(opts: {wrongGroup?: boolean, mutableTag?: boolean, missingStep?: boolean} = {}) {
  const Block = record({st: oneOf('absent', 'unloaded', 'loaded'), readers: nat, tag: nat, charge: nat})
  const r = rule('DuckDB persistent registered block reservation')
    .inputs({op: oneOf('register', 'load', 'pin', 'unpin', 'evictSelected', 'lastReference'), id: nat, tag: nat, size: nat})
    .state({totalMem: 0})
    .maps({TagMem: 0, B: Block.from({st: 'absent', readers: 0, tag: 0, charge: 0})})
    .flags(({op, id, size, B}) => {
      const b = B.at(id)
      return {
        registers: op.is('register').and(b.st.is('absent')),
        loads: op.is('load').and(b.st.is('unloaded'), size.gt(0)),
        pins: op.is('pin').and(b.st.is('loaded')),
        unpins: op.is('unpin').and(b.st.is('loaded'), b.readers.gt(0)),
        evicts: op.is('evictSelected').and(b.st.is('loaded'), b.readers.eq(0)),
        destroys: op.is('lastReference').and(b.st.is('absent').not(), b.readers.eq(0)),
      }
    })
    .step(({id, tag, size, totalMem, TagMem, B, registers, loads, pins, unpins, evicts, destroys}) => {
      const b = B.at(id), frees = evicts.or(destroys)
      const tagAddr = opts.wrongGroup ? b.tag.plus(1) : b.tag
      const used = TagMem.at(tagAddr)
      return {
        totalMem: when(loads, totalMem.plus(size), when(frees, totalMem.minus(b.charge), totalMem)),
        TagMem: opts.missingStep
          ? TagMem.set(tagAddr, when(frees, used.minus(b.charge), used))
          : TagMem.set(tagAddr, when(loads, used.plus(size), when(frees, used.minus(b.charge), used))),
        B: B.set(id, {
          st: when(destroys, 'absent', when(loads, 'loaded', when(registers.or(evicts), 'unloaded', b.st))),
          readers: when(loads, 1, when(pins, b.readers.plus(1), when(unpins, b.readers.minus(1), b.readers))),
          tag: opts.mutableTag
            ? when(registers.or(pins), tag, when(destroys, 0, b.tag))
            : when(registers, tag, when(destroys, 0, b.tag)),
          charge: when(loads, size, when(frees, 0, b.charge)),
        }),
      }
    })
  const law = r.law('every loaded block memory charge is covered by its tag memory total', ({B, TagMem}) =>
    forall(k => B.at(k).st.is('loaded').implies(B.at(k).charge.atMost(TagMem.at(B.at(k).tag)))))
  return {r, law}
}

function makeNATS(opts: {requirePositiveSubj?: boolean} = {}) {
  const Msg = record({present: bool, subj: nat, size: nat})
  const r = rule('NATS JetStream memStore')
    .params({maxMsgs: nat, maxBytes: nat})
    .inputs({op: oneOf('store', 'remove'), seq: nat, subj: nat, contentSize: nat})
    .state({msgs: 0, bytes: 0, lastSeq: 0})
    .maps({M: Msg.from({present: false, subj: 0, size: 0}), SubjMsgs: 0})
    .flags(({op, seq, subj, contentSize, maxMsgs, maxBytes, msgs, bytes, M}) => ({
      stores: op.is('store').and(
        subj.eq(0).or(contentSize.gt(0)),
        maxMsgs.eq(0).or(msgs.lt(maxMsgs)),
        maxBytes.eq(0).or(bytes.plus(contentSize).plus(16).atMost(maxBytes)),
      ),
      removes: op.is('remove').and(M.at(seq).present),
    }))
    .step(({op, seq, subj, contentSize, msgs, bytes, lastSeq, M, SubjMsgs, stores, removes}) => {
      const nextSeq = lastSeq.plus(1)
      const size = contentSize.plus(16)
      const rm = M.at(seq)
      const msgKey = when(op.is('store'), nextSeq, seq)
      const subjKey = when(op.is('store'), subj, rm.subj)
      const decOk = removes.and(msgs.gt(0))
      return {
        msgs: when(stores, msgs.plus(1), when(decOk, msgs.minus(1), msgs)),
        bytes: when(stores, bytes.plus(size), when(decOk, bytes.minus(rm.size), bytes)),
        lastSeq: when(stores, nextSeq, lastSeq),
        M: M.set(msgKey, {
          present: choose(stores, yes, choose(removes, no, M.at(msgKey).present)),
          subj: when(stores, subj, when(removes, 0, M.at(msgKey).subj)),
          size: when(stores, size, when(removes, 0, M.at(msgKey).size)),
        }),
        SubjMsgs: SubjMsgs.set(subjKey, when(stores.and(subjKey.gt(0)), SubjMsgs.at(subjKey).plus(1),
          when(removes.and(subjKey.gt(0)), SubjMsgs.at(subjKey).minus(1), SubjMsgs.at(subjKey)))),
      }
    })
  const law = opts.requirePositiveSubj === false
    ? r.law('every stored message has a positive subject count even for empty subject', ({M, SubjMsgs}) =>
      forall(k => M.at(k).present.implies(SubjMsgs.at(M.at(k).subj).atLeast(1))))
    : r.law('every stored message has a positive stream count and, for nonempty subjects, a positive subject count', ({M, msgs, SubjMsgs}) =>
      forall(k => M.at(k).present.implies(msgs.atLeast(1).and(M.at(k).subj.gt(0).implies(SubjMsgs.at(M.at(k).subj).atLeast(1))))))
  return {r, law}
}

function proveHandCert(source: Machine, law: Law, spec: Omit<GroupedSumCertificate, 'kind' | 'proof'>): GroupedSumCertificate {
  const dummy: GroupedSumCertificate = {kind: 'grouped-sum', ...spec, proof: {instances: {}, trees: {}}}
  const theory = groupedSumTheory(source, law, dummy)
  if (!theory) throw new Error('groupedSumTheory rejected valid spec')
  const out = proveLaws(theory.plain, spec.laws)
  if (!out.proven || !out.checked || !out.proof) throw new Error(`proveLaws failed: ${out.failed?.goal} ${out.failed?.stuck}`)
  const trees: Record<string, Tree> = {...out.proof.trees}
  for (const g of [...theory.initGoals, ...theory.coverGoals]) {
    const r = grow(g)
    if (!('tree' in r)) throw new Error(`side goal ${g.name} failed`)
    trees[g.name] = r.tree
  }
  return {kind: 'grouped-sum', ...spec, proof: {instances: out.proof.instances, trees}}
}

describe('grouped-sum trusted rule', () => {
  for (const [id, build] of [['DuckDB16', () => makeDuckDB()], ['NATS7', () => makeNATS()]] as const) {
    test(`proves ${id} by default and exports Lean`, () => {
      const {r, law} = build()
      let ev: PublicProofOutput | undefined
      proofOutput.on = e => { ev = e }
      const v = proveRule(r as never, [law])
      proofOutput.on = undefined
      expect(v.proven).toBe(true)
      expect(v.checked).toBe(true)
      const agg = findAgg(ev?.proof)
      expect(agg?.certificate.kind).toBe('grouped-sum')
      expect(checkGroupedSum(agg!.machine, agg!.law, agg!.certificate as GroupedSumCertificate)).toBe(true)
      const lean = toLean([{id, aggregate: {source: agg!.machine, law: agg!.law, certificate: agg!.certificate, kinds: agg!.kinds}}])
      expect(lean).toContain('import GroupedSums')
      expect(lean).toContain('theorem packet_shape : packet_psums.plain = packet_machine := by rfl')
      expect(lean).toContain('theorem original_law')
      expect(lean).toContain(`#print axioms ${id}_kinds_laws`)
    }, 30_000)
  }

  test('rejects all 5 required domain mutants (wrong group, changing group key, mutable param, missing step, empty group)', () => {
    // Capture a valid DuckDB certificate to also test cross-machine certificate rejection.
    const validDuck = makeDuckDB()
    let validEv: PublicProofOutput | undefined
    proofOutput.on = e => { validEv = e }
    const validV = proveRule(validDuck.r as never, [validDuck.law])
    proofOutput.on = undefined
    expect(validV.proven && validV.checked).toBe(true)
    const validAgg = findAgg(validEv?.proof)!
    const validCert = validAgg.certificate as GroupedSumCertificate

    // 1. Row counted in the wrong group
    const wrongGroup = makeDuckDB({wrongGroup: true})
    const vWrong = proveRule(wrongGroup.r as never, [wrongGroup.law], {search: {ms: 5000}})
    expect(vWrong.proven).toBe(false)
    expect(checkGroupedSum(wrongGroup.r.machine, wrongGroup.law, validCert)).toBe(false)
    // Also reject a forged cert whose sum filters B.tag[k] = obs + 1
    const s0Name = Object.keys(validCert.sums)[0]!
    const s0 = validCert.sums[s0Name]!
    const wrongFilterCert: GroupedSumCertificate = {
      ...validCert,
      sums: {
        [s0Name]: {
          ...s0,
          term: ite({
            op: 'and',
            xs: [
              same(get('B.st', x(s0.key)), n(2)),
              same(get('B.tag', x(s0.key)), plus(x(validCert.observer), n(1))),
            ],
          }, get('B.charge', x(s0.key)), n(0)),
        },
      },
    }
    expect(checkGroupedSum(validAgg.machine, validAgg.law, wrongFilterCert)).toBe(false)

    // 2. Group key that changes over time without migrating totals
    const mutTag = makeDuckDB({mutableTag: true})
    const vMutTag = proveRule(mutTag.r as never, [mutTag.law], {search: {ms: 5000}})
    expect(vMutTag.proven).toBe(false)
    expect(checkGroupedSum(mutTag.r.machine, mutTag.law, validCert)).toBe(false)

    // 3. Sum that reads a mutable parameter (state variable or input)
    const mutStateMachine: Machine = {
      name: 'mutable-param-test',
      params: [],
      inputs: ['k', 'inp'],
      state: {dyn: n(0)},
      maps: {M: 0},
      step: {
        state: {dyn: plus(x('dyn'), n(1))},
        maps: {M: {key: x('k'), value: n(1)}},
      },
    }
    const falseLaw: Law = {name: 'false', forall: 'j', holds: same(get('M', x('j')), n(0))}
    const mutParamCert: GroupedSumCertificate = {
      kind: 'grouped-sum',
      observer: 'obs',
      group: get('M', x('j')),
      sums: {S: {key: 'sk', params: ['dyn'], term: ite(same(get('M', x('sk')), x('dyn')), n(1), n(0))}},
      laws: [{name: 'false', forall: 'j', holds: {op: 'or', xs: [not(same(get('M', x('j')), x('obs'))), falseLaw.holds]}}],
      proof: {instances: {}, trees: {}},
    }
    expect(checkGroupedSum(mutStateMachine, falseLaw, mutParamCert)).toBe(false)
    const mutInputCert: GroupedSumCertificate = {
      ...mutParamCert,
      sums: {S: {key: 'sk', params: ['inp'], term: ite(same(get('M', x('sk')), x('inp')), n(1), n(0))}},
    }
    expect(checkGroupedSum(mutStateMachine, falseLaw, mutInputCert)).toBe(false)
    // Reading state var without listing in params (M1)
    const unlistedVarCert: GroupedSumCertificate = {
      ...mutParamCert,
      sums: {S: {key: 'sk', params: ['obs'], term: ite(same(get('M', x('sk')), x('dyn')), n(1), n(0))}},
    }
    expect(checkGroupedSum(mutStateMachine, falseLaw, unlistedVarCert)).toBe(false)

    // 4. Missing per-group step (broken machine + missing cover key in cert)
    const missingStep = makeDuckDB({missingStep: true})
    const vMissing = proveRule(missingStep.r as never, [missingStep.law], {search: {ms: 5000}})
    expect(vMissing.proven).toBe(false)
    expect(checkGroupedSum(missingStep.r.machine, missingStep.law, validCert)).toBe(false)
    const missingCoverCert: GroupedSumCertificate = {
      ...validCert,
      sums: {[s0Name]: {...s0, covers: []}},
    }
    expect(checkGroupedSum(validAgg.machine, validAgg.law, missingCoverCert)).toBe(false)

    // 5. Empty group: missing present/loaded guard (nonzero at obs = 0 -> @init fails) + NATS empty subject
    const emptyGroupIntegrand: GroupedSumCertificate = {
      ...validCert,
      sums: {
        [s0Name]: {
          ...s0,
          term: ite(same(get('B.tag', x(s0.key)), x(validCert.observer)), n(1), n(0)),
        },
      },
    }
    expect(checkGroupedSum(validAgg.machine, validAgg.law, emptyGroupIntegrand)).toBe(false)
    const natsEmptySubj = makeNATS({requirePositiveSubj: false})
    const vEmpty = proveRule(natsEmptySubj.r as never, [natsEmptySubj.law], {search: {ms: 5000}})
    expect(vEmpty.proven).toBe(false)
  }, 30_000)

  test('supports pre-guarded parameterized sums, each-writes with @cover + pcellLaws, and scalar observer_elim', () => {
    // Positive M9 control: pre-guarded parameterized sum where p > 0 ensures atStart = 0.
    const preMachine: Machine = {
      name: 'pre-guarded-sum',
      params: ['p'],
      inputs: ['k'],
      pre: {op: '<', a: n(0), b: x('p')},
      state: {cnt: n(0)},
      maps: {M: 0},
      step: {
        state: {cnt: ite(same(get('M', x('k')), x('p')), x('cnt'), plus(x('cnt'), n(1)))},
        maps: {M: {key: x('k'), value: x('p')}},
      },
    }
    const preLaw: Law = {
      name: 'p-cell implies positive cnt',
      forall: 'j',
      holds: {op: 'or', xs: [not(same(get('M', x('j')), x('p'))), atMost(n(1), x('cnt'))]},
    }
    const preCert = proveHandCert(preMachine, preLaw, {
      observer: 'obs',
      group: get('M', x('j')),
      sums: {S: {key: 'sk', params: ['p'], term: ite(same(get('M', x('sk')), x('p')), n(1), n(0))}},
      laws: [
        {name: 'S <= cnt', holds: atMost(x('S'), x('cnt'))},
        {name: preLaw.name, forall: 'j', holds: {op: 'or', xs: [not(same(get('M', x('j')), x('obs'))), preLaw.holds]}},
      ],
    })
    expect(checkGroupedSum(preMachine, preLaw, preCert)).toBe(true)
    // Dropping pre breaks @init because at p = 0, ite(0 = 0, 1, 0) = 1 != 0!
    expect(checkGroupedSum({...preMachine, pre: undefined}, preLaw, preCert)).toBe(false)
    // Dropping @init tree must be rejected (M8)
    const noInitTrees = {...preCert.proof.trees}
    delete noInitTrees['S @init']
    expect(checkGroupedSum(preMachine, preLaw, {...preCert, proof: {...preCert.proof, trees: noInitTrees}})).toBe(false)

    // Positive each-write control with @cover goal + pcellLaws + Lean export
    const eachMachine: Machine = {
      name: 'each-grouped-sum',
      params: [],
      inputs: ['id', 'tag'],
      state: {},
      maps: {Flag: 0, Tag: 0, Tot: 0},
      step: {
        flags: {add: same(get('Flag', x('id')), n(0))},
        maps: {
          Flag: {each: 'e', value: ite({op: 'and', xs: [{op: 'flag', name: 'add'}, same(x('e'), x('id'))]}, n(1), get('Flag', x('e')))},
          Tag: {key: x('id'), value: ite({op: 'flag', name: 'add'}, x('tag'), get('Tag', x('id')))},
          Tot: {key: x('tag'), value: ite({op: 'flag', name: 'add'}, plus(get('Tot', x('tag')), n(1)), get('Tot', x('tag')))},
        },
      },
    }
    const eachLaw: Law = {
      name: 'flagged implies tot >= 1',
      forall: 'j',
      holds: {op: 'or', xs: [not(same(get('Flag', x('j')), n(1))), atMost(n(1), get('Tot', get('Tag', x('j'))))]},
    }
    const eachCert = proveHandCert(eachMachine, eachLaw, {
      observer: 'obs',
      group: get('Tag', x('j')),
      sums: {
        S: {
          key: 'sk',
          params: ['obs'],
          term: ite({op: 'and', xs: [same(get('Flag', x('sk')), n(1)), same(get('Tag', x('sk')), x('obs'))]}, n(1), n(0)),
        },
      },
      laws: [
        {name: 'S <= Tot[obs]', holds: atMost(x('S'), get('Tot', x('obs')))},
        {name: eachLaw.name, forall: 'j', holds: {op: 'or', xs: [not(same(get('Tag', x('j')), x('obs'))), eachLaw.holds]}},
      ],
    })
    expect(checkGroupedSum(eachMachine, eachLaw, eachCert)).toBe(true)
    const eachLean = groupedSumToLean('EachTest', eachMachine, eachLaw, eachCert)
    expect(eachLean).toContain('packet_covers')
    // Removing @cover tree must be rejected
    const noCoverTrees = {...eachCert.proof.trees}
    delete noCoverTrees['S @cover Flag']
    expect(checkGroupedSum(eachMachine, eachLaw, {...eachCert, proof: {...eachCert.proof, trees: noCoverTrees}})).toBe(false)
    // Unsound each-write (modifies all keys without being in cover) must be rejected
    const badEach: Machine = {
      ...eachMachine,
      step: {...eachMachine.step, maps: {...eachMachine.step.maps, Flag: {each: 'e', value: n(1)}}},
    }
    expect(checkGroupedSum(badEach, eachLaw, eachCert)).toBe(false)

    // Positive scalar law control (l.key = none branch of observer_elim)
    const scalarMachine: Machine = {
      name: 'scalar-observer',
      params: [],
      inputs: ['k'],
      state: {cur: n(0)},
      maps: {A: 0, Tot: 0},
      step: {
        state: {cur: x('k')},
        maps: {
          A: {key: x('k'), value: plus(get('A', x('k')), n(1))},
          Tot: {key: x('k'), value: plus(get('Tot', x('k')), n(1))},
        },
      },
    }
    const scalarLaw: Law = {
      name: 'cur cell at most Tot[cur]',
      holds: atMost(get('A', x('cur')), get('Tot', x('cur'))),
    }
    const scalarCert = proveHandCert(scalarMachine, scalarLaw, {
      observer: 'obs',
      group: x('cur'),
      sums: {S: {key: 'sk', params: ['obs'], term: ite(same(get('A', x('sk')), n(0)), n(0), n(0))}},
      laws: [
        {name: 'A <= Tot at obs', holds: atMost(get('A', x('obs')), get('Tot', x('obs')))},
        {name: scalarLaw.name, holds: {op: 'or', xs: [not(same(x('cur'), x('obs'))), scalarLaw.holds]}},
      ],
    })
    expect(checkGroupedSum(scalarMachine, scalarLaw, scalarCert)).toBe(true)
    const scalarLean = groupedSumToLean('ScalarTest', scalarMachine, scalarLaw, scalarCert)
    expect(scalarLean).toContain('def unchangedLaw : MLaw :=')
    expect(scalarLean).toContain(', none⟩')
  }, 30_000)

  test('kills all checker guard mutants (M3, M6-M18, structural/tamper refusals)', () => {
    const base: Machine = {
      name: 'guard-tests',
      params: ['p'],
      inputs: ['k'],
      state: {v: n(0)},
      maps: {M: 0, T: 0},
      step: {
        state: {v: x('v')},
        maps: {
          M: {key: x('k'), value: n(1)},
          T: {key: x('k'), value: plus(get('T', x('k')), n(1))},
        },
      },
    }
    const okLaw: Law = {name: 'triv', forall: 'j', holds: atMost(n(0), get('T', get('M', x('j'))))}
    const goodCert = proveHandCert(base, okLaw, {
      observer: 'obs',
      group: get('M', x('j')),
      sums: {S: {key: 'sk', params: ['obs'], term: ite(same(get('M', x('sk')), n(2)), n(1), n(0))}},
      laws: [
        {name: okLaw.name, forall: 'j', holds: {op: 'or', xs: [not(same(get('M', x('j')), x('obs'))), okLaw.holds]}},
      ],
    })
    expect(checkGroupedSum(base, okLaw, goodCert)).toBe(true)

    // M3: latent-branch tup and proj in sum term must be refused
    const tupTerm: E = ite(same(n(0), n(1)), {op: 'tup', a: get('M', x('sk')), b: x('obs')}, n(0))
    const projTerm: E = ite(same(n(0), n(1)), {op: 'proj', k: 0, a: get('M', x('sk'))}, n(0))
    expect(groupedSumTheory(base, okLaw, {...goodCert, sums: {S: {key: 'sk', params: ['obs'], term: tupTerm}}})).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {...goodCert, sums: {S: {key: 'sk', params: ['obs'], term: projTerm}}})).toBeUndefined()

    // M6: paramImmutable refuses summation binder sk in sum.params
    expect(groupedSumTheory(base, okLaw, {
      ...goodCert,
      sums: {S: {key: 'sk', params: ['sk'], term: ite(same(get('M', x('sk')), n(2)), x('sk'), n(0))}},
    })).toBeUndefined()

    // M7: paramImmutable refuses cover key x$S in sum.params
    expect(groupedSumTheory(base, okLaw, {
      ...goodCert,
      sums: {S: {key: 'sk', params: ['x$S'], term: ite(same(get('M', x('sk')), n(2)), x('x$S'), n(0))}},
    })).toBeUndefined()

    // M10: symbolic parameter atStart check rejects ite(M[k]=0 && obs=1, 1, 0) (0 at obs=0, 1 at obs=1!)
    const m10Cert: GroupedSumCertificate = {
      ...goodCert,
      sums: {S: {key: 'sk', params: ['obs'], term: ite({op: 'and', xs: [same(get('M', x('sk')), n(0)), same(x('obs'), n(1))]}, n(1), n(0))}},
    }
    const m10Theory = groupedSumTheory(base, okLaw, m10Cert)!
    expect(m10Theory).toBeDefined()
    expect('tree' in grow(m10Theory.initGoals[0]!)).toBe(false)
    expect(checkGroupedSum(base, okLaw, m10Cert)).toBe(false)

    // M11: pcellLaws skips a law whose forall binder collides with a sum parameter
    const eachBase: Machine = {
      name: 'm11-each',
      params: ['p'],
      inputs: ['k'],
      state: {},
      maps: {M: 0},
      step: {maps: {M: {each: 'e', value: ite(same(x('e'), x('k')), n(1), get('M', x('e')))}}},
    }
    const m11Law: Law = {name: 'l', forall: 'j', holds: atMost(n(0), get('M', x('j')))}
    const m11Theory = groupedSumTheory(eachBase, m11Law, {
      kind: 'grouped-sum',
      observer: 'obs',
      group: get('M', x('j')),
      sums: {S: {key: 'sk', params: ['p'], term: ite({op: 'and', xs: [same(get('M', x('sk')), n(1)), same(x('p'), n(1))]}, n(1), n(0))}},
      laws: [
        {name: 'shadowed', forall: 'p', holds: same(get('M', x('p')), n(0))},
        {name: 'l', forall: 'j', holds: {op: 'or', xs: [not(same(get('M', x('j')), x('obs'))), m11Law.holds]}},
      ],
      proof: {instances: {}, trees: {}},
    })!
    // The shadowed law (forall: 'p' where 'p' is in sum.params) must NOT appear in cover goal hyps!
    expect(m11Theory.coverGoals.length).toBe(1)
    expect(JSON.stringify(m11Theory.coverGoals[0]!.hyps)).not.toContain('"map":"M","key":{"op":"var","name":"x$S"}},"b":{"op":"const","value":0}')

    // M12: observerOk rejects obs constrained by source.pre
    const preObs: Machine = {...base, params: ['p', 'obs'], pre: {op: '<', a: n(0), b: x('obs')}}
    expect(checkGroupedSum(preObs, okLaw, goodCert)).toBe(false)
    // Also rejects undeclared obs occurring in source.pre
    expect(checkGroupedSum({...base, pre: {op: '<', a: n(0), b: x('obs')}}, okLaw, goodCert)).toBe(false)

    // M13: observerOk rejects obs in source.assume, source.step, or source.state
    expect(checkGroupedSum({...base, params: ['p', 'obs'], assume: same(x('k'), x('obs'))}, okLaw, goodCert)).toBe(false)
    expect(checkGroupedSum({...base, params: ['p', 'obs'], state: {v: x('obs')}}, okLaw, goodCert)).toBe(false)
    expect(checkGroupedSum({...base, params: ['p', 'obs'], step: {...base.step, state: {v: x('obs')}}}, okLaw, goodCert)).toBe(false)

    // M14: observerOk rejects obs in source.facts
    const withFact: Machine = {
      ...base,
      params: ['p', 'obs'],
      fns: {f: {js: 'x => x'}},
      facts: [{name: 'f-obs', holds: same(get('f', x('obs')), n(0))}],
    }
    expect(checkGroupedSum(withFact, okLaw, goodCert)).toBe(false)

    // M15: hkey rejects law.forall === obs (fixed-point unsoundness!), even when cert.group avoids obs
    const obsForallLaw: Law = {name: 'fp', forall: 'obs', holds: same(get('M', x('obs')), n(99))}
    expect(groupedSumTheory(base, obsForallLaw, {
      ...goodCert,
      observer: 'obs',
      group: x('v'),
      laws: [{name: 'fp', forall: 'obs', holds: {op: 'or', xs: [not(same(x('v'), x('obs'))), obsForallLaw.holds]}}],
    })).toBeUndefined()

    // M16: hgrp rejects cert.group mentioning obs (vacuously UNSAT guard obs + 1 = obs!)
    const falseTarget: Law = {name: 'false-vacuous', forall: 'j', holds: same(n(0), n(1))}
    const unsatGroup: E = plus(x('obs'), n(1))
    const vacuousGuard: Law = {
      name: 'false-vacuous',
      forall: 'j',
      holds: {op: 'or', xs: [not(same(unsatGroup, x('obs'))), falseTarget.holds]},
    }
    const fakePlain: Machine = {...base, params: ['p', 'obs']}
    const vacuousProof = proveLaws(fakePlain, [vacuousGuard])
    expect(vacuousProof.proven && vacuousProof.checked).toBe(true) // Guard alone IS trivially provable!
    // Must be REJECTED by both groupedSumTheory and checkGroupedSum because cert.group mentions obs!
    const m16Cert: GroupedSumCertificate = {
      ...goodCert,
      group: unsatGroup,
      laws: [vacuousGuard],
      proof: {instances: vacuousProof.proof!.instances, trees: {...vacuousProof.proof!.trees, 'S @init': goodCert.proof.trees['S @init']!}},
    }
    expect(groupedSumTheory(base, falseTarget, m16Cert)).toBeUndefined()
    expect(checkGroupedSum(base, falseTarget, m16Cert)).toBe(false)

    // M17: hlo rejects law.holds mentioning obs
    const baseWithObsParam: Machine = {...base, params: ['p', 'obs']}
    const lawReadsObs: Law = {name: 'reads-obs', forall: 'j', holds: same(get('M', x('j')), x('obs'))}
    expect(checkGroupedSum(baseWithObsParam, lawReadsObs, {
      ...goodCert,
      laws: [{name: 'reads-obs', forall: 'j', holds: {op: 'or', xs: [not(same(get('M', x('j')), x('obs'))), lawReadsObs.holds]}}],
    })).toBe(false)

    // M18: sghostOk / avoids rejects sum colliding with source or guardLaw reading S / ?cells$S
    expect(groupedSumTheory({...base, state: {v: n(0), S: n(0)}}, okLaw, goodCert)).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {
      ...goodCert,
      group: x('S'),
      laws: [{name: okLaw.name, forall: 'j', holds: {op: 'or', xs: [not(same(x('S'), x('obs'))), okLaw.holds]}}],
    })).toBeUndefined()

    // Extra structural & tamper refusals
    expect(checkGroupedSum(base, okLaw, {...goodCert, kind: 'ghost-write' as never})).toBe(false)
    expect(checkGroupedSum(base, okLaw, {...goodCert, sums: {}})).toBe(false)
    expect(checkGroupedSum(base, okLaw, {...goodCert, laws: []})).toBe(false)
    // Missing exact guardLaw
    expect(checkGroupedSum(base, okLaw, {
      ...goodCert,
      laws: [{name: okLaw.name, forall: 'j', holds: okLaw.holds}],
    })).toBe(false)
    // Sum reading both a real map and a carried map / function / prototype property must be rejected
    const withInputMap: Machine = {...base, inputMaps: ['IM']}
    expect(groupedSumTheory(withInputMap, okLaw, {
      ...goodCert,
      sums: {S: {key: 'sk', params: ['obs'], term: plus(get('M', x('sk')), get('IM', x('sk')))}},
    })).toBeUndefined()
    const withFn: Machine = {...base, fns: {fn1: {js: 'x => x'}}}
    expect(groupedSumTheory(withFn, okLaw, {
      ...goodCert,
      sums: {S: {key: 'sk', params: ['obs'], term: plus(get('M', x('sk')), get('fn1', x('sk')))}},
    })).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {
      ...goodCert,
      sums: {S: {key: 'sk', params: ['obs'], term: get('toString', x('sk'))}},
    })).toBeUndefined()
    // Non-safe map default (passes Number.isInteger in obligations, fails safeNat in groupedSumTheory)
    expect(groupedSumTheory({...base, maps: {M: 0, T: 2 ** 53}}, okLaw, goodCert)).toBeUndefined()
    // Reserved names, duplicate params, worddiv$ (with matching guardLaw!), negative constants/mul, cover keys
    expect(groupedSumTheory(base, okLaw, {...goodCert, observer: 'bad?obs'})).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {...goodCert, observer: ''})).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {...goodCert, observer: '1'})).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {...goodCert, sums: {S: {...goodCert.sums.S!, params: ['obs', 'obs']}}})).toBeUndefined()
    const wordGrp = get('worddiv$u64$q', x('j'))
    expect(groupedSumTheory(base, okLaw, {
      ...goodCert,
      group: wordGrp,
      laws: [{name: okLaw.name, forall: 'j', holds: {op: 'or', xs: [not(same(wordGrp, x('obs'))), okLaw.holds]}}],
    })).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {...goodCert, sums: {S: {...goodCert.sums.S!, term: n(-1)}}})).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {...goodCert, sums: {S: {...goodCert.sums.S!, term: {op: 'mul', k: -1, a: get('M', x('sk'))}}}})).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {...goodCert, sums: {S: {...goodCert.sums.S!, covers: [x('k'), x('sk')]}}})).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {...goodCert, sums: {S: {...goodCert.sums.S!, covers: [x('k'), x('x$S')]}}})).toBeUndefined()
    // paramSumTermOk / paramSumCondOk operator mutants (get key mismatch, add/eq one-sided bad var, flag/all in cond, and with one bad branch)
    expect(groupedSumTheory(base, okLaw, {...goodCert, sums: {S: {key: 'sk', params: ['obs'], term: get('M', x('obs'))}}})).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {...goodCert, sums: {S: {key: 'sk', params: ['obs'], term: get('M', plus(x('sk'), n(1)))}}})).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {...goodCert, sums: {S: {key: 'sk', params: ['obs'], term: plus(get('M', x('sk')), x('v'))}}})).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {...goodCert, sums: {S: {key: 'sk', params: ['obs'], term: plus(x('v'), get('M', x('sk')))}}})).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {...goodCert, sums: {S: {key: 'sk', params: ['obs'], term: ite({op: 'flag', name: 'f'}, n(1), n(0))}}})).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {...goodCert, sums: {S: {key: 'sk', params: ['obs'], term: ite({op: 'all', key: 'q', c: same(n(0), n(0))}, n(1), n(0))}}})).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {...goodCert, sums: {S: {key: 'sk', params: ['obs'], term: ite({op: 'and', xs: [same(get('M', x('sk')), n(1)), same(x('v'), n(0))]}, n(1), n(0))}}})).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {...goodCert, sums: {S: {key: 'sk', params: ['obs'], term: ite(same(get('M', x('sk')), x('v')), n(1), n(0))}}})).toBeUndefined()
    // Group term containing a flag or quantifier must be rejected
    expect(groupedSumTheory({...base, step: {...base.step, flags: {f: same(x('k'), n(0))}}}, okLaw, {
      ...goodCert,
      group: ite({op: 'flag', name: 'f'}, n(1), n(0)),
      laws: [{name: okLaw.name, forall: 'j', holds: {op: 'or', xs: [not(same(ite({op: 'flag', name: 'f'}, n(1), n(0)), x('obs'))), okLaw.holds]}}],
    })).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {
      ...goodCert,
      group: ite({op: 'all', key: 'q', c: same(n(0), n(0))}, n(1), n(0)),
    })).toBeUndefined()
    // Cover key containing a flag must be rejected
    expect(groupedSumTheory({...base, step: {...base.step, flags: {f: same(x('k'), n(0))}}}, okLaw, {
      ...goodCert,
      sums: {S: {...goodCert.sums.S!, covers: [x('k'), ite({op: 'flag', name: 'f'}, n(1), n(0))]}},
    })).toBeUndefined()
    // Unsupported source/law features must each be refused individually
    expect(groupedSumTheory({...base, primitiveFailure: same(n(0), n(1))}, okLaw, goodCert)).toBeUndefined()
    expect(groupedSumTheory({...base, sums: {Z: {key: 'zk', term: get('M', x('zk'))}}}, okLaw, goodCert)).toBeUndefined()
    expect(groupedSumTheory({...base, counts: {C: {j: 'cj', key: 'ck', below: n(1), body: n(1)}}}, okLaw, goodCert)).toBeUndefined()
    expect(groupedSumTheory({...base, leasts: {L: {some: 's', key: 'lk', where: same(n(0), n(0)), by: [{e: n(0)}]}}}, okLaw, goodCert)).toBeUndefined()
    expect(groupedSumTheory({...base, history: {keep: same(n(0), n(0)), record: ['k'], sums: {}, queries: {}}}, okLaw, goodCert)).toBeUndefined()
    expect(groupedSumTheory(base, {...okLaw, keys: ['j2']}, goodCert)).toBeUndefined()
    expect(groupedSumTheory(base, {...okLaw, some: ['w']}, goodCert)).toBeUndefined()
    expect(groupedSumTheory(base, {...okLaw, finite: 'p'}, goodCert)).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {...goodCert, laws: [...goodCert.laws, {name: 'ex-helper', holds: same(n(0), n(0)), some: ['w']}]})).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {...goodCert, laws: [...goodCert.laws, {name: 'fin-helper', forall: 'j', holds: {op: 'or', xs: [not({op: '<', a: x('j'), b: x('p')}), same(n(0), n(0))]}, finite: 'p'}]})).toBeUndefined()
    // pcellLaws must skip a law that reads both a summed map and an unsummed map
    const mReadBoth: Machine = {
      name: 'pcell-unsummed',
      params: [],
      inputs: ['k'],
      state: {},
      maps: {M: 0, Other: 0},
      step: {maps: {M: {each: 'e', value: ite(same(x('e'), x('k')), n(1), get('M', x('e')))}}},
    }
    const thBoth = groupedSumTheory(mReadBoth, {name: 'l', forall: 'j', holds: atMost(n(0), get('M', x('j')))}, {
      kind: 'grouped-sum',
      observer: 'obs',
      group: get('M', x('j')),
      sums: {S: {key: 'sk', params: ['obs'], term: ite({op: 'and', xs: [same(get('M', x('sk')), n(1)), same(x('obs'), n(1))]}, n(1), n(0))}},
      laws: [
        {name: 'reads-other', forall: 'j', holds: atMost(get('M', x('j')), get('Other', x('j')))},
        {name: 'l', forall: 'j', holds: {op: 'or', xs: [not(same(get('M', x('j')), x('obs'))), atMost(n(0), get('M', x('j')))]}},
      ],
      proof: {instances: {}, trees: {}},
    })!
    expect(JSON.stringify(thBoth.coverGoals[0]!.hyps)).not.toContain('"map":"Other"')
    // Multi-cover-key sum (2 distinct point-written maps at k1 and k2) must be accepted (kills .some -> .every on cover check)
    const twoKeyM: Machine = {
      name: 'two-cover-keys',
      params: [],
      inputs: ['k1', 'k2'],
      state: {},
      maps: {A: 0, B: 0, Tot: 0},
      step: {
        maps: {
          A: {key: x('k1'), value: n(0)},
          B: {key: x('k2'), value: n(0)},
          Tot: {key: x('k1'), value: get('Tot', x('k1'))},
        },
      },
    }
    const twoKeyLaw: Law = {name: 'triv2', forall: 'j', holds: atMost(n(0), get('Tot', get('A', x('j'))))}
    const twoKeyCert = proveHandCert(twoKeyM, twoKeyLaw, {
      observer: 'obs',
      group: get('A', x('j')),
      sums: {S: {key: 'sk', params: ['obs'], term: ite({op: 'and', xs: [same(get('A', x('sk')), n(1)), same(get('B', x('sk')), x('obs'))]}, n(1), n(0))}},
      laws: [{name: twoKeyLaw.name, forall: 'j', holds: {op: 'or', xs: [not(same(get('A', x('j')), x('obs'))), twoKeyLaw.holds]}}],
    })
    expect(checkGroupedSum(twoKeyM, twoKeyLaw, twoKeyCert)).toBe(true)
    // Machine with a quantified flag beside a plain flag and an each write
    const qflagEach: Machine = {
      name: 'qflag-each',
      params: [],
      inputs: ['id'],
      state: {},
      maps: {M: 0, T: 0},
      step: {
        flags: {
          allZero: {op: 'all', key: 'qk', c: same(get('M', x('qk')), n(0))},
          go: {op: 'and', xs: [{op: 'flag', name: 'allZero'}, same(get('M', x('id')), n(0))]},
        },
        maps: {
          M: {each: 'e', value: ite({op: 'and', xs: [{op: 'flag', name: 'go'}, same(x('id'), x('e'))]}, n(0), get('M', x('e')))},
          T: {key: x('id'), value: get('T', x('id'))},
        },
      },
    }
    const qfLaw: Law = {name: 'qf-triv', forall: 'j', holds: atMost(n(0), get('T', get('M', x('j'))))}
    const qfCert = proveHandCert(qflagEach, qfLaw, {
      observer: 'obs',
      group: get('M', x('j')),
      sums: {S: {key: 'sk', params: ['obs'], term: ite({op: 'and', xs: [same(get('M', x('sk')), n(1)), same(x('obs'), n(1))]}, n(1), n(0))}},
      laws: [{name: qfLaw.name, forall: 'j', holds: {op: 'or', xs: [not(same(get('M', x('j')), x('obs'))), qfLaw.holds]}}],
    })
    expect(checkGroupedSum(qflagEach, qfLaw, qfCert)).toBe(true)
    const qfTh = groupedSumTheory(qflagEach, qfLaw, qfCert)!
    expect(JSON.stringify(qfTh.coverGoals[0]!.hyps)).toContain('"name":"?allZero"')
    expect(JSON.stringify(qfTh.coverGoals[0]!.hyps)).not.toContain('"op":"flag"')
    // Observer colliding with quantified flag's bound key must be rejected
    expect(groupedSumTheory(qflagEach, qfLaw, {
      ...qfCert,
      observer: 'qk',
      sums: {S: {key: 'sk', params: ['qk'], term: ite({op: 'and', xs: [same(get('M', x('sk')), n(1)), same(x('qk'), n(1))]}, n(1), n(0))}},
      laws: [{name: qfLaw.name, forall: 'j', holds: {op: 'or', xs: [not(same(get('M', x('j')), x('qk'))), qfLaw.holds]}}],
    })).toBeUndefined()
    // Exporter refuses invalid cert and invalid Lean identifier, and stays on decide +kernel even under GDP_LEAN_NATIVE=1
    expect(() => groupedSumToLean('123bad', base, okLaw, goodCert)).toThrow(/invalid grouped-sum export/)
    expect(() => groupedSumToLean('BadCert', base, okLaw, {...goodCert, sums: {}})).toThrow(/invalid grouped-sum export/)
    const prevNative = process.env.GDP_LEAN_NATIVE
    process.env.GDP_LEAN_NATIVE = '1'
    try {
      const leanStrict = groupedSumToLean('StrictKernel', base, okLaw, goodCert)
      expect(leanStrict).toContain('decide +kernel')
      expect(leanStrict).not.toContain('native_decide')
    } finally {
      if (prevNative === undefined) delete process.env.GDP_LEAN_NATIVE
      else process.env.GDP_LEAN_NATIVE = prevNative
    }
    // Reject tuple-arity maps, worddiv$ smuggled in cert.proof.instances, and cover keys reading sum ghosts
    const tupleM: Machine = {
      name: 'tuple-map',
      params: [],
      inputs: ['a', 'b'],
      state: {},
      maps: {M: 0, T: 0},
      step: {
        maps: {
          M: {key: {op: 'tup', a: x('a'), b: x('b')}, value: n(1)},
          T: {key: x('a'), value: get('T', x('a'))},
        },
      },
    }
    expect(groupedSumTheory(tupleM, {name: 'tl', forall: 'j', holds: atMost(n(0), get('T', x('j')))}, goodCert)).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {
      ...goodCert,
      proof: {...goodCert.proof, instances: {[okLaw.name]: {[okLaw.name]: [get('worddiv$q8', x('k'))]}}},
    })).toBeUndefined()
    expect(groupedSumTheory(base, okLaw, {
      ...goodCert,
      sums: {S: {...goodCert.sums.S!, covers: [x('k'), x('S')]}},
    })).toBeUndefined()
    // Ensure obligations still works cleanly on base
    expect(obligations(base, [okLaw]).length).toBe(2)
  })
})
