# CHC-COMP candidates for the next frontier corpus

From the 0.20.0 gap analysis of CHC-COMP 2026's LIA-Lin track (`compare/chc/README.md`, section 0.20.0): tasks that
Spacer, Golem or Eldarica solve within 60 s and gdp-wired doesn't, grouped by what gdp-wired lacks, the smallest and
most readable of each group first. Every figure is from `runs/modal/chc2/` (`gap-v020.json`, written by
`compare/chc/prof/gap.py`).

How an entry reads:

- the task (its `.yml` in `chc-comp/chc-comp26-benchmarks` at `b4fa7a7`), its size, the slots of gdp-wired's rule
  (`translate.ts`: a predicate's Int arguments are `i0, i1, ...` and its Bool ones `b0, b1, ...`, in order) and the
  predicates;
- Spacer's invariant (Z3 5.3.1, `prof/spacer_models.py`): each predicate's interpretation in CNF over linear atoms,
  in those slot names, the first four clauses; it is one invariant, not necessarily the simplest;
- its class (its most demanding clause against `inferLaws`' templates for that task, `prof/template.ts`), the goal
  gdp-wired's run stopped on, and what `proveRule` did given Spacer's invariant as laws (`prof/given.ts`);
- for unsat tasks, the length of Golem's derivation of false (0.9.0, `--print-witness`) beside gdp-wired's guided runs.

## A. The step goal of a small invariant over a wide transition (Lustre; 195 tasks)

Spacer's invariant is within the templates (most often one yes/no value); on 73 of the 195, the goal gdp-wired's search
stopped on is one of its conjuncts. Given that invariant as laws, the kernel leaves its step goal undecided at the
prover's per-goal time budget. The rule is one predicate over tens of Int and Bool slots whose step is a guarded update
of every slot. Lacking: deciding such a step goal within the budget (the goal reads one slot; the step's case splits
are over all of them).

- `vmt-chc-benchmarks/lustre/DRAGON_10_000_001.yml` (32,913 bytes, 78 Int and 32 Bool slots, 1 predicate)
  - Spacer: state: b19
  - class: bound; gdp-wired stopped on `loc is p0 → 1 <= b19 @step unknown`; given Spacer's invariant: not proven: an invariant conjunct's goal undecided (unknown, the time budget) (38,696 ms)
- `vmt-chc-benchmarks/lustre/SYNAPSE_all_000_001.yml` (7,616 bytes, 33 Int and 12 Bool slots, 1 predicate)
  - Spacer: state: b8
  - class: bound; gdp-wired stopped on `loc is p0 → i4 + 1 <= b8 @step unknown`; given Spacer's invariant: not proven: an invariant conjunct's goal undecided (unknown, the time budget) (20,358 ms)
- `vmt-chc-benchmarks/lustre/MESI_all_000_001.yml` (10,239 bytes, 44 Int and 13 Bool slots, 1 predicate)
  - Spacer: state: b8
  - class: bound; gdp-wired stopped on `loc is p0 → i2 + 3 <= i0 @step unknown`; given Spacer's invariant: not proven: an invariant conjunct's goal undecided (unknown, the time budget) (20,413 ms)
- `vmt-chc-benchmarks/lustre/MESI_3_000_001.yml` (11,825 bytes, 52 Int and 13 Bool slots, 1 predicate)
  - Spacer: state: b11
  - class: bound; gdp-wired stopped on `loc is p0 → i1 + 3 <= i0 @step unknown`; given Spacer's invariant: not proven: an invariant conjunct's goal undecided (unknown, the time budget) (20,467 ms)
- `vmt-chc-benchmarks/lustre/MOESI_2_e8_101_000_001.yml` (11,646 bytes, 50 Int and 17 Bool slots, 1 predicate)
  - Spacer: state: b12
  - class: bound; gdp-wired stopped on `loc is p0 → 1 <= b11 @step unknown`; given Spacer's invariant: not proven: an invariant conjunct's goal undecided (unknown, the time budget) (23,113 ms)
- `vmt-chc-benchmarks/lustre/MESI_i3_e1_447_e3_1180_000_001.yml` (10,037 bytes, 44 Int and 13 Bool slots, 1 predicate)
  - Spacer: state: b8; state: i6 <= i4
  - class: two values; gdp-wired stopped on `loc is p0 → i2 + 1 <= b8 @step unknown`; given Spacer's invariant: not proven: an invariant conjunct's goal undecided (unknown, the time budget) (20,450 ms)
- `vmt-chc-benchmarks/lustre/fast_1_e8_747_000.yml` (9,218 bytes, 1 Int and 62 Bool slots, 1 predicate)
  - Spacer: state: b53
  - class: bound; gdp-wired stopped on `loc is p0 → 1 <= b48 @step unknown`; given Spacer's invariant: not proven: an invariant conjunct's goal undecided (unknown, the time budget) (56,514 ms)
- `vmt-chc-benchmarks/lustre/metros_1_000_001.yml` (9,827 bytes, 26 Int and 41 Bool slots, 1 predicate)
  - Spacer: state: b22; state: b29; state: b20 or not b0; state: i1 + 1 <= i4 or not b8 … (5 clauses in all)
  - class: a yes/no guard; gdp-wired stopped on `loc is p0 → 1 <= b0 @step unknown`; given Spacer's invariant: not proven: an invariant conjunct's goal undecided (unknown, the time budget) (55,016 ms)
- `vmt-chc-benchmarks/lustre/FIREFLY_5_e2_2229_000_001.yml` (19,259 bytes, 55 Int and 21 Bool slots, 1 predicate)
  - Spacer: state: b12
  - class: bound; gdp-wired stopped on `loc is p0 → i2 + 1 <= b12 @step unknown`; given Spacer's invariant: not proven: an invariant conjunct's goal undecided (unknown, the time budget) (26,988 ms)
- `vmt-chc-benchmarks/lustre/fast_2_000_001.yml` (12,732 bytes, 1 Int and 83 Bool slots, 1 predicate)
  - Spacer: state: b74; state: b76 or not b75; state: b21 or not b2; state: b78 or not b75
  - class: a yes/no guard; gdp-wired stopped on `loc is p0 → 1 <= b62 @step unknown`; given Spacer's invariant: not proven: an invariant conjunct's goal undecided (unknown, the time budget) (55,092 ms)
- `vmt-chc-benchmarks/lustre/MOESI_all_000_001.yml` (11,839 bytes, 50 Int and 17 Bool slots, 1 predicate)
  - Spacer: state: b12; state: i6 <= 1; state: b6 or not b0
  - class: a yes/no guard; gdp-wired stopped on `loc is p0 → 1 <= b11 @step unknown`; given Spacer's invariant: not proven: an invariant conjunct's goal undecided (unknown, the time budget) (39,195 ms)

## B. Lustre, within the templates, proven once given (41 tasks)

Given Spacer's invariant, the kernel proves it; gdp-wired's search didn't find it. Its runs reach few states on these
rules (a random request rarely meets a clause's wide guard; a guided run makes a few steps a trial), so tens of
thousands of candidates stay alive and the counterexample-driven choice goes elsewhere. Lacking: reachable-state
sampling on wide rules, and a choice that prefers what the law's counterexample reads.

- `vmt-chc-benchmarks/lustre/hysteresis_2_000_001.yml` (3,390 bytes, 9 Int and 12 Bool slots, 1 predicate)
  - Spacer: state: b9; state: 1 <= i1 or not b1
  - class: a yes/no guard; gdp-wired stopped on `0 <= i7 + 3 @step unknown`; given Spacer's invariant: proven (9,603 ms)
- `vmt-chc-benchmarks/lustre/hysteresis_3_000_001.yml` (3,390 bytes, 9 Int and 12 Bool slots, 1 predicate)
  - Spacer: state: b9; state: not b0 or not b1; state: i1 + 1 <= 0 or not b0
  - class: a yes/no guard; gdp-wired stopped on `loc is p0 → b1 + 1 <= b9 @step unknown`; given Spacer's invariant: proven (10,161 ms)
- `vmt-chc-benchmarks/lustre/hysteresis_all_000_001.yml` (3,611 bytes, 9 Int and 13 Bool slots, 1 predicate)
  - Spacer: state: b10; state: 0 <= i1 + 1 or not b1; state: i1 <= 0 or not b0
  - class: a yes/no guard; gdp-wired stopped on `loc is p0 → 1 <= b10 @step unknown`; given Spacer's invariant: proven (9,221 ms)
- `vmt-chc-benchmarks/lustre/car_4_e8_118_e7_178_000_001.yml` (5,051 bytes, 13 Int and 22 Bool slots, 1 predicate)
  - Spacer: state: 0 <= i1; state: b21
  - class: bound; gdp-wired stopped on `loc is p0 → 1 <= i1 + b21 @step unknown`; given Spacer's invariant: proven (20,391 ms)
- `vmt-chc-benchmarks/lustre/car_3_e8_33_e7_220_000_001.yml` (5,181 bytes, 13 Int and 22 Bool slots, 1 predicate)
  - Spacer: state: b21; state: b0 or not b13
  - class: a yes/no guard; gdp-wired stopped on `loc is p0 → b11 + 1 <= b21 @step unknown`; given Spacer's invariant: proven (17,525 ms)
- `vmt-chc-benchmarks/lustre/car_2_e8_491_e7_826_000_001.yml` (5,184 bytes, 13 Int and 22 Bool slots, 1 predicate)
  - Spacer: state: b21; state: i2 <= 10; state: b0 or b7
  - class: a yes/no guard; gdp-wired stopped on `loc is p0 → b13 + 1 <= b21 @step unknown`; given Spacer's invariant: proven (10,965 ms)
- `vmt-chc-benchmarks/lustre/PRODUCER_CONSUMER_2_000_001.yml` (5,807 bytes, 29 Int and 11 Bool slots, 1 predicate)
  - Spacer: state: b6; state: 0 <= i10 or i0 + 1 <= 0
  - class: a disjunction of two (a counterexample's form); gdp-wired stopped on `loc is p0 → 1 <= i4 + b6 @step unknown`; given Spacer's invariant: proven (8,944 ms)
- `vmt-chc-benchmarks/lustre/SYNAPSE_4_e8_420_e7_572_000_001.yml` (6,779 bytes, 31 Int and 11 Bool slots, 1 predicate)
  - Spacer: state: b7; state: i2 <= 0 or i4 <= 0
  - class: a disjunction of two (a counterexample's form); gdp-wired stopped on `loc is p0 → 1 <= b7 @step unknown`; given Spacer's invariant: proven (20,131 ms)
- `vmt-chc-benchmarks/lustre/SYNAPSE_123_000_001.yml` (7,910 bytes, 33 Int and 15 Bool slots, 1 predicate)
  - Spacer: state: b11
  - class: bound; gdp-wired stopped on `loc is p0 → 1 <= b11 @step unknown`; given Spacer's invariant: proven (20,552 ms)
- `vmt-chc-benchmarks/lustre/metros_1_e2_1102_e8_311_000.yml` (9,724 bytes, 26 Int and 41 Bool slots, 1 predicate)
  - Spacer: state: b22; state: b29
  - class: bound; gdp-wired stopped on `loc is p0 → 1 <= b0 @step unknown`; given Spacer's invariant: proven (25,743 ms)
- `vmt-chc-benchmarks/lustre/MESI_4_e7_1140_e7_433_000_001.yml` (10,156 bytes, 44 Int and 13 Bool slots, 1 predicate)
  - Spacer: state: b8; state: i6 <= 0
  - class: bound; gdp-wired stopped on `loc is p0 → i2 + 3 <= i0 @step unknown`; given Spacer's invariant: proven (24,624 ms)
- `vmt-chc-benchmarks/lustre/MOESI_1_000_001.yml` (11,258 bytes, 50 Int and 15 Bool slots, 1 predicate)
  - Spacer: state: b10; state: 2 <= i6 or not b7; state: b7 or i6 <= 1
  - class: a yes/no guard; gdp-wired stopped on `loc is p0 → i7 + 1 <= b10 @step unknown`; given Spacer's invariant: proven (16,227 ms)

## C. Guards over several yes/no values: a program counter in bits (38 tasks; 33 proven once given)

The `ctigar` tasks (C programs as transition systems) encode the program counter in yes/no slots, and the invariant is
"at this pc, a bound": `not b2 or not b3 or 1 <= i1`. `inferLaws` guards a form by one value (a choice, a yes/no or a
small natural), so a guard of two yes/no values beside a linear literal is no candidate. Lacking: guards by a
conjunction of yes/no values (or the bits read as one choice).

- `vmt-chc-benchmarks/ctigar/simple.c_000_001.yml` (1,863 bytes, 2 Int and 4 Bool slots, 1 predicate)
  - Spacer: state: not b0 or not b3; state: not b2 or not b3; state: i0 <= i1 or not b2; state: b2 or b3 or i0 <= 0 or not b0 … (5 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `b3 is yes → 1 <= i1 @step unknown`; given Spacer's invariant: proven (9,255 ms)
- `vmt-chc-benchmarks/ctigar/dillig07.c_000.yml` (2,378 bytes, 3 Int and 4 Bool slots, 1 predicate)
  - Spacer: state: i1 <= i2 or not b2; state: i1 <= i2 or not b3; state: i1 <= i0 or not b2; state: not b2 or not b3 … (10 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `b1 is no → i1 <= i0 @step unknown`; given Spacer's invariant: proven (12,122 ms)
- `vmt-chc-benchmarks/ctigar/simple_nest.c_000_001.yml` (2,386 bytes, 3 Int and 4 Bool slots, 1 predicate)
  - Spacer: state: 1 <= i0 or b1; state: 1 <= i0 or not b2; state: not b2 or not b3; state: 1 <= i0 or b2 or not b0 … (5 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `loc is p0 → i1 <= i0 + 8 → b0 + b1 + b3 <= 1 @step unknown`; given Spacer's invariant: proven (8,457 ms)
- `vmt-chc-benchmarks/ctigar/up-nested.c_000_001.yml` (2,612 bytes, 4 Int and 4 Bool slots, 1 predicate)
  - Spacer: state: 0 <= i0 or not b0; state: 0 <= i0 or not b2; state: 0 <= i0 or not b3; state: not b2 or not b3 … (5 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `loc is p0 → b1 + 1 <= b2 → b0 + i1 <= i3 + 1 @step unknown`; given Spacer's invariant: proven (8,133 ms)
- `vmt-chc-benchmarks/ctigar/simple_if.c_000_001.yml` (2,625 bytes, 3 Int and 4 Bool slots, 1 predicate)
  - Spacer: state: 1 <= i0 or b1; state: 1 <= i0 or not b2; state: 1 <= i0 or not b0; state: not b2 or not b3 … (6 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `b0 is yes → 1 <= i0 @step unknown`; given Spacer's invariant: proven (9,620 ms)
- `vmt-chc-benchmarks/ctigar/nested.c_000_001.yml` (3,034 bytes, 4 Int and 4 Bool slots, 1 predicate)
  - Spacer: state: 1 <= i1 or not b0; state: 1 <= i1 or not b2; state: not b2 or not b3; state: 1 <= i1 or b1 or b2 or b3 … (6 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `b2 is never yes @step unknown`; given Spacer's invariant: proven (10,339 ms)
- `vmt-chc-benchmarks/ctigar/dillig28.c_000.yml` (3,354 bytes, 3 Int and 4 Bool slots, 1 predicate)
  - Spacer: state: i2 <= i0 or not b2; state: i2 <= i0 or not b0; state: i0 <= i2 or not b3; state: i0 <= i2 + 1 or not b2 … (15 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `loc is p0 → 1 <= i0 → b3 + b0 <= 1 @step unknown`; given Spacer's invariant: proven (27,478 ms)
- `vmt-chc-benchmarks/ctigar/nested1.c_000_001.yml` (3,387 bytes, 4 Int and 4 Bool slots, 1 predicate)
  - Spacer: state: 1 <= i2 or not b3; state: 1 <= i2 or not b2; state: not b0 or not b1 or not b3
  - class: a disjunction of three or more; gdp-wired stopped on `b2 + b3 <= 0 @step unknown`; given Spacer's invariant: proven (8,284 ms)
- `vmt-chc-benchmarks/conc/szymanski_safe_000.yml` (4,174 bytes, 2 Int and 8 Bool slots, 1 predicate)
  - Spacer: state: 2 <= i1 or not b0 or not b7; state: 2 <= i1 or b6 or not b1; state: 4 <= i0 or b4 or not b2; state: b4 or b6 or not b1 or not b2 … (5 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `b3 is yes → 3 <= i0 @step unknown`; given Spacer's invariant: proven (14,445 ms)
- `vmt-chc-benchmarks/ctigar/nest-if.c_000_001.yml` (4,399 bytes, 3 Int and 5 Bool slots, 1 predicate)
  - Spacer: state: 1 <= i1 or b1; state: not b2 or not b4; state: not b3 or not b4; state: 2 <= i1 or not b1 or not b4 … (8 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `b1 is no → 2·i0 <= i1 + 1 @step sat`; given Spacer's invariant: proven (16,017 ms)
- `vmt-chc-benchmarks/ctigar/id_build.c_000_001.yml` (4,546 bytes, 5 Int and 4 Bool slots, 1 predicate)
  - Spacer: state: 0 <= i4 or not b3; state: b3 or i4 + 1 <= i3 or not b2; state: b2 or i4 + 1 <= i3 or not b3; state: 0 <= i4 or not b0 or not b1 … (10 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `b3 is yes → 0 <= i0 + i3 @step unknown`; given Spacer's invariant: proven (18,842 ms)
- `vmt-chc-benchmarks/ctigar/bound.c_000_001.yml` (9,390 bytes, 6 Int and 5 Bool slots, 1 predicate)
  - Spacer: state: 0 <= i0 or not b4; state: not b3 or not b4; state: 0 <= i0 or not b0 or not b3; state: 0 <= i0 or b0 or not b3 … (8 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `loc is p0 → b3 <= 0 @step unknown`; given Spacer's invariant: proven (16,625 ms)
- `vmt-chc-benchmarks/lustre/durationThm_3_000_001.yml` (2,519 bytes, 15 Int and 6 Bool slots, 1 predicate)
  - Spacer: state: i0 <= i4; state: b3; state: i0 <= i2 + i8 or not b0; state: 0 <= i2 + i8 or i8 <= 0 … (5 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `i0 <= i4 @step unknown`; given Spacer's invariant: proven (8,385 ms)
- `vmt-chc-benchmarks/lustre/durationThm_1_000_001.yml` (2,664 bytes, 15 Int and 8 Bool slots, 1 predicate)
  - Spacer: state: i1 <= i4; state: 0 <= i2; state: b4; state: i1 <= i2 + i8 or not b0 … (5 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `loc is p0 → i8 <= 2 → i8 + b0 + i2 <= 3 @step unknown`; given Spacer's invariant: proven (7,922 ms)

## D. Disjunctions of two or more linear literals (116 tasks: 73 of three or more, 43 of two beside yes/no values)

Case-split invariants: `i0 + 1 <= i2 or i1 <= i3 or i2 + 1 <= i0` (`reve/014`), Spacer's interpolants in the
`extra-small-lia` tasks. A counterexample's forms take one condition and one body; past that no candidate exists.
Lacking: clauses of several linear literals, generalized from counterexamples (IC3-style), not enumerated.

- `extra-small-lia/s_multipl_24_000.yml` (1,253 bytes, 4 Int and 0 Bool slots, 2 predicates)
  - Spacer: SAD: i3 <= i0 + 3; SAD: i3 <= i1; SAD: 0 <= i2; SAD: i2 <= 1 … (16 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `3·i1 <= 4·i2 + 2·i3 + 1 @step unknown`; given Spacer's invariant: proven (4,668 ms)
- `vmt-chc-benchmarks/ctigar/gulwani_fig1a.c_000_001.yml` (1,785 bytes, 2 Int and 4 Bool slots, 1 predicate)
  - Spacer: state: not b0 or not b3; state: not b2 or not b3; state: not b1 or not b3; state: 1 <= i1 or i0 + 50 <= 0 or not b0 … (6 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `b2 is yes → i1 <= b0 + 10 @step unknown`; given Spacer's invariant: proven (10,179 ms)
- `vmt-chc-benchmarks/ctigar/pldi08.c_000.yml` (1,840 bytes, 2 Int and 4 Bool slots, 1 predicate)
  - Spacer: state: not b0 or not b3; state: not b2 or not b3; state: not b1 or not b3; state: 0 <= i1 or i0 + 50 <= 0 or not b0 … (7 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `loc is p0 → i0 + i1 <= 0 → i0 + i1 + b0 <= 0 @step unknown`; given Spacer's invariant: proven (9,055 ms)
- `vmt-chc-benchmarks/ctigar/dillig01.c_000.yml` (2,607 bytes, 4 Int and 4 Bool slots, 1 predicate)
  - Spacer: state: 1 <= i3 or not b0; state: 1 <= i3 or not b3; state: not b2 or not b3; state: 1 <= i3 or not b2 … (12 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `b3 is yes → 3 <= i2 + 2·i3 @step unknown`; given Spacer's invariant: proven (19,274 ms)
- `extra-small-lia/gj2007_m_3_000.yml` (2,645 bytes, 4 Int and 0 Bool slots, 5 predicates)
  - Spacer: inv2: i3 <= i0; inv2: i2 <= i0; inv2: i3 <= i1; inv2: i0 + 3 <= 5·i3 … (51 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `loc is p1 → 8 <= i1 + 7·i3 @step unknown`; given Spacer's invariant: proven (33,104 ms)
- `eldarica-misc/LIA/reve/014-horn_000.yml` (2,648 bytes, 4 Int and 0 Bool slots, 4 predicates)
  - Spacer: REC_f_f: i0 + 1 <= i2 or i3 <= i1; REC_f_f: i0 + 1 <= i2 or i1 <= i3 or i2 + 1 <= i0; REC_f_: i0 <= i1; REC_f_: 1 <= i0 or i1 <= 0
  - class: a disjunction of three or more; gdp-wired stopped on `loc is p1 → 4 <= i1 → 6 <= i1 @step unknown`; given Spacer's invariant: proven (5,744 ms)
- `eldarica-misc/LIA/reve/015-horn_000.yml` (3,936 bytes, 4 Int and 0 Bool slots, 4 predicates)
  - Spacer: REC_f_f: i0 + 1 <= i2 or i0 <= i3 + 1 or i2 + 1 <= i0; REC_f_f: i0 + 1 <= i2 or i1 <= i3 or i2 + 1 <= i0; REC_f_f: i0 + 1 <= i2 or i2 + 1 <= i0 or i3 <= i1
  - class: a disjunction of three or more; gdp-wired stopped on `loc is p1 → i1 + 1 <= i3 → i0 + 1 <= i2 @step unknown`; given Spacer's invariant: proven (10,295 ms)
- `eldarica-misc/LIA/reve/013-horn_000.yml` (4,028 bytes, 4 Int and 0 Bool slots, 4 predicates)
  - Spacer: REC_f_f: i1 <= i3 or i2 + 1 <= i0; REC_f_f: i0 + 1 <= i2 or i2 + 1 <= i0 or i3 <= i1; REC__f: i0 <= i1; REC__f: 2 <= i0 or i1 <= i0
  - class: a disjunction of three or more; gdp-wired stopped on `loc is p1 → i2 <= 7 → i3 <= 21 @step unknown`; given Spacer's invariant: proven (12,023 ms)
- `vmt-chc-benchmarks/ctigar/dillig15.c_000.yml` (3,598 bytes, 4 Int and 4 Bool slots, 1 predicate)
  - Spacer: state: i3 <= i1 + i2 or not b3; state: 0 <= i2 or not b3; state: 0 <= i2 or 1 <= i3 or not b2; state: i3 <= i1 + i2 or not b0 or not b2 … (11 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `loc is p0 → b2 <= 0 @step unknown`; given Spacer's invariant: proven (24,224 ms)
- `vmt-chc-benchmarks/ctigar/dillig37.c_000.yml` (3,830 bytes, 3 Int and 5 Bool slots, 1 predicate)
  - Spacer: state: not b4; state: 0 <= i1 or b1; state: 0 <= i1 or not b3; state: 0 <= i1 or not b2 … (14 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `b3 is yes → 0 <= 3·i1 + 2·i2 @step unknown`; given Spacer's invariant: proven (23,510 ms)
- `vmt-chc-benchmarks/ctigar/ex1.c_000.yml` (5,290 bytes, 4 Int and 5 Bool slots, 1 predicate)
  - Spacer: state: not b4; state: 0 <= i0 + 2·i1 or not b0; state: 0 <= i0 + 2·i1 or b1; state: 0 <= i2 or b2 or not b3 … (8 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `loc is p0 → i2 <= 0 → i2 + b3 + 1 <= b1 @step unknown`; given Spacer's invariant: proven (18,124 ms)
- `vmt-chc-benchmarks/ctigar/dillig19.c_000.yml` (6,430 bytes, 4 Int and 5 Bool slots, 1 predicate)
  - Spacer: state: not b3 or not b4; state: i1 + 1 <= i0 or i3 <= i0 or not b4; state: i0 <= i1 + 1 or i3 + 1 <= i0 or not b4; state: i3 <= i1 or i3 <= i2 or not b4 … (23 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `loc is p0 → b3 + b4 <= 0 @step unknown`; given Spacer's invariant: not proven: an invariant conjunct's goal undecided (unknown, the time budget) (55,031 ms)
- `hcai-bench/svcomp/O3/O3_Addition03_true-unreach-call_true-no-overflow_true-termination_000.yml` (4,521 bytes, 4 Int and 0 Bool slots, 3 predicates)
  - Spacer: main@.lr.ph.i: 1 <= i2 or i2 + 1 <= 0; main@.lr.ph.i: 0 <= i2 or i1 <= 99; main@.lr.ph.i: 100 <= i3 or i0 <= 99 or i1 <= 99; main@.lr.ph.i: 179 <= i3 or 22 <= i2 or i0 <= 99 or i1 <= 99 … (102 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `i0 <= i3 @step unknown`; given Spacer's invariant: not proven: an invariant conjunct's goal undecided (unknown, the time budget) (55,002 ms)
- `extra-small-lia/s_mutants_16_m_000.yml` (1,018 bytes, 3 Int and 0 Bool slots, 2 predicates)
  - Spacer: itp: 3 <= i1; itp: i1 <= 112; itp: i0 <= 100; itp: 0 <= i0 … (130 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `3·i0 <= i1 + 120·i2 + 117 @step unknown`; given Spacer's invariant: not proven: out of the 60 s
- `vmt-chc-benchmarks/lustre/twisted_counters_000_001.yml` (2,113 bytes, 5 Int and 12 Bool slots, 1 predicate)
  - Spacer: state: 0 <= i0; state: i0 <= 5; state: b11; state: 4 <= i0 or not b6 … (16 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `b1 is yes → 3·b2 + 2 <= i4 @step unknown`; given Spacer's invariant: proven (14,181 ms)
- `vmt-chc-benchmarks/lustre/cd_000_001.yml` (3,101 bytes, 7 Int and 16 Bool slots, 1 predicate)
  - Spacer: state: b15; state: i0 <= 14 or not b3; state: i1 <= 0 or not b0; state: i1 <= 7 or not b3 … (17 clauses in all)
  - class: a disjunction of three or more; gdp-wired stopped on `i1 + b7 <= 7 @step unknown`; given Spacer's invariant: not proven: an invariant conjunct's goal undecided (unknown, the time budget) (55,321 ms)

## E. More than three values in one atom (71 tasks; 32 Lustre)

The relational tasks (`reve`, `llreve`: two programs side by side) need sums and differences across both programs'
variables, `i0 + i4 <= i1 + i3`, often with coefficients 2 to 8 (`barthe2-big`). The templates stop at three values
(±1 only, on most rules, past their limits). Lacking: forms over four or more values, taken from the clauses' own
linear terms (the differences the transition preserves) rather than enumerated.

- `extra-small-lia/three_dots_moving_2_000.yml` (843 bytes, 4 Int and 0 Bool slots, 1 predicate)
  - Spacer: inv: i1 + i2 <= 2·i0 + i3; inv: i1 <= i2 + i3; inv: i0 <= i1
  - class: more than three values in one atom; gdp-wired stopped on `loc is p0 → i0 + 2 <= i2 → i1 + 4 <= i2 + i3 @step unknown`; given Spacer's invariant: proven (4,712 ms)
- `llreve-bench/smt2/loop__barthe2_000_002.yml` (1,338 bytes, 6 Int and 0 Bool slots, 1 predicate)
  - Spacer: INV_MAIN_1: i3 + i5 <= 2·i0 + i2 + 1; INV_MAIN_1: i1 + i3 <= i0 + i4 + 1; INV_MAIN_1: i2 + 1 <= i3 + i5; INV_MAIN_1: i5 <= i0 + i2 … (10 clauses in all)
  - class: more than three values in one atom; gdp-wired stopped on `no clause derives false @step unknown`; given Spacer's invariant: proven (42,993 ms)
- `eldarica-misc/LIA/reve/004-horn_000.yml` (1,402 bytes, 6 Int and 0 Bool slots, 1 predicate)
  - Spacer: INV1: i5 <= i1 + i2; INV1: i0 + i4 <= i1 + i3 + 1; INV1: 2·i0 + i2 <= 2·i3 + i5; INV1: i2 + 1 <= i4 + i5 … (10 clauses in all)
  - class: more than three values in one atom; gdp-wired stopped on `2·i5 <= 3·i2 + i4 @step unknown`; given Spacer's invariant: proven (26,163 ms)
- `llreve-bench/smt2/clausified/loop__fib_000_001.yml` (1,452 bytes, 6 Int and 0 Bool slots, 1 predicate)
  - Spacer: INV_MAIN_42: i2 <= i5 + 1; INV_MAIN_42: 1 <= i2 or i5 <= 0; INV_MAIN_42: i0 + i1 <= i4 or i2 <= 0; INV_MAIN_42: i2 <= 0 or i4 <= i0 + i1 … (9 clauses in all)
  - class: more than three values in one atom; gdp-wired stopped on `loc is p0 → i1 + 1 <= i4 → 1 <= i2 @step unknown`; given Spacer's invariant: proven (6,665 ms)
- `llreve-bench/smt2/loop__loop3_000_002.yml` (1,468 bytes, 6 Int and 0 Bool slots, 1 predicate)
  - Spacer: INV_MAIN_42: i2 <= i5; INV_MAIN_42: i0 + i4 <= i1 + i3; INV_MAIN_42: i5 <= i2 + 2; INV_MAIN_42: i0 + 1 <= i1 or i2 + 2 <= i5 … (7 clauses in all)
  - class: more than three values in one atom; gdp-wired stopped on `i5 <= 2·i0 @step unknown`; given Spacer's invariant: proven (8,311 ms)
- `llreve-bench/smt2/clausified/loop__loop2_000_001.yml` (1,499 bytes, 6 Int and 0 Bool slots, 1 predicate)
  - Spacer: INV_MAIN_42: i0 + i5 <= i2 + i3 + 1; INV_MAIN_42: i1 <= i4; INV_MAIN_42: i4 <= i1; INV_MAIN_42: i2 + i3 + 1 <= i0 + i5
  - class: more than three values in one atom; gdp-wired stopped on `i0 + 2·i2 <= 2·i5 + 2 @step unknown`; given Spacer's invariant: proven (4,443 ms)
- `eldarica-misc/LIA/reve/017-horn_000.yml` (1,542 bytes, 6 Int and 0 Bool slots, 1 predicate)
  - Spacer: INV1: i1 + i3 <= i0 + i4 + 1; INV1: i5 <= i2; INV1: i0 + i4 + 1 <= i1 + i3; INV1: i2 <= i5
  - class: more than three values in one atom; gdp-wired stopped on `2·i0 + i1 <= 2·i3 + 2 @step unknown`; given Spacer's invariant: proven (6,035 ms)
- `llreve-bench/smt2/loop__barthe_000_002.yml` (1,565 bytes, 8 Int and 0 Bool slots, 1 predicate)
  - Spacer: INV_MAIN_42: i2 + i4 <= i1 + i6; INV_MAIN_42: i3 <= i7; INV_MAIN_42: i0 + 5·i1 + i3 <= i5 + i7; INV_MAIN_42: i1 + i6 <= i2 + i4 … (6 clauses in all)
  - class: more than three values in one atom; gdp-wired stopped on `i7 <= i1 + i3 @step unknown`; given Spacer's invariant: proven (31,953 ms)
- `eldarica-misc/LIA/reve/010-horn_000.yml` (1,720 bytes, 8 Int and 0 Bool slots, 1 predicate)
  - Spacer: INV1: i0 <= i4 + 1; INV1: 1 <= i0 or i2 <= i6; INV1: i0 <= i4 or i1 + i2 <= i6; INV1: 1 <= i0 or i6 <= i2 … (8 clauses in all)
  - class: more than three values in one atom; gdp-wired stopped on `loc is p0 → i2 + 1 <= i6 → 1 <= i0 @start unknown`; given Spacer's invariant: proven (11,157 ms)
- `eldarica-misc/LIA/reve/003-horn_000.yml` (2,189 bytes, 10 Int and 0 Bool slots, 1 predicate)
  - Spacer: INV1: i9 <= i4; INV1: i4 <= i9; INV1: i8 + i9 <= i1 + 5·i2 + i4; INV1: i0 + i7 <= i2 + i5 … (6 clauses in all)
  - class: more than three values in one atom; gdp-wired stopped on `i4 <= i9 @step unknown`; given Spacer's invariant: proven (24,684 ms)
- `hcai-bench/svcomp/O3/O3_sum_non_true-unreach-call_true-termination_000.yml` (2,958 bytes, 4 Int and 0 Bool slots, 3 predicates)
  - Spacer: main@tailrecurse.i: i2 + i3 <= i0 + i1; main@tailrecurse.i: i0 + i1 <= i2 + i3; main@tailrecurse.i: i3 + 1 <= i0 + i1
  - class: more than three values in one atom; gdp-wired stopped on `loc is never p2 @step unknown`; given Spacer's invariant: proven (23,020 ms)
- `llreve-bench/smt2/loop__barthe2-big_000_002.yml` (2,466 bytes, 6 Int and 0 Bool slots, 2 predicates)
  - Spacer: INV_MAIN_2: 3·i3 + i5 <= 4·i0 + i2 + 3; INV_MAIN_2: 4·i3 + i5 <= 5·i0 + i2 + 4; INV_MAIN_2: i1 + i3 <= i0 + i4 + 1; INV_MAIN_2: i5 <= 2·i0 + i2 … (21 clauses in all)
  - class: more than three values in one atom; gdp-wired stopped on `no clause derives false @step unknown`; given Spacer's invariant: not proven: out of the 60 s
- `llreve-bench/smt2/clausified/loop__barthe2-big3_000_001.yml` (4,600 bytes, 6 Int and 0 Bool slots, 4 predicates)
  - Spacer: INV_MAIN_4: 6·i0 + i1 <= 6·i2 + i3; INV_MAIN_4: i3 <= i1; INV_MAIN_4: i0 <= 1 or i2 <= i0; INV_MAIN_4: 7 <= i2 or i1 <= i3 … (36 clauses in all)
  - class: more than three values in one atom; gdp-wired stopped on `loc is p1 → 4 <= i1 + 3·i3 @step unknown`; given Spacer's invariant: not proven: an invariant conjunct's goal undecided (unknown, the time budget) (55,048 ms)
- `vmt-chc-benchmarks/lustre/SYNAPSE_5_000_001.yml` (6,928 bytes, 33 Int and 11 Bool slots, 1 predicate)
  - Spacer: state: b7; state: i6 + i8 <= i0; state: i4 + i6 + i8 <= i0; state: b5 or not b0 … (5 clauses in all)
  - class: more than three values in one atom; gdp-wired stopped on `loc is p0 → 1 <= b7 @step unknown`; given Spacer's invariant: not proven: an invariant conjunct's goal undecided (unknown, the time budget) (20,271 ms)
- `vmt-chc-benchmarks/lustre/SYNAPSE_3_e7_425_000_001.yml` (7,126 bytes, 33 Int and 11 Bool slots, 1 predicate)
  - Spacer: state: i4 + i6 + i8 <= i0; state: i0 <= i4 + i6 + i8; state: b7
  - class: more than three values in one atom; gdp-wired stopped on `loc is p0 → i4 + 1 <= b7 @step unknown`; given Spacer's invariant: not proven: an invariant conjunct's goal undecided (unknown, the time budget) (20,325 ms)

## F. What a gdp-wired law can't state here (45 tasks)

Spacer's invariant reads a remainder or a quotient (18: `(mod x 2) = 0` for a counter stepping by 2) or keeps an
existential from its projection (27). Laws over this rule state neither: the rule reads no `modBy(c)`/`divBy(c)`, a CHC
integer is a pair of naturals, and a law has no quantifier over values. Lacking: a remainder term over an integer slot
(a quotient in the state, or the remainders of both parts with their facts), and quantifier elimination for the
projected ones.

- `extra-small-lia/const_mod_1_000.yml` (431 bytes, 1 Int and 0 Bool slots, 1 predicate)
  - Spacer: inv: <mod>
  - class: mod; gdp-wired stopped on `no clause derives false @step unknown`; given Spacer's invariant: a conjunct gdp-wired can't state here (mod) (59 ms)
- `extra-small-lia/const_mod_2_000.yml` (439 bytes, 1 Int and 0 Bool slots, 1 predicate)
  - Spacer: inv: <mod>
  - class: mod; gdp-wired stopped on `no clause derives false @step unknown`; given Spacer's invariant: a conjunct gdp-wired can't state here (mod) (47 ms)
- `extra-small-lia/const_mod_3_000.yml` (549 bytes, 2 Int and 0 Bool slots, 1 predicate)
  - Spacer: inv: 0 <= i1; inv: i1 <= 1; inv: <mod> or i1 <= 0; inv: 1 <= i1 or <mod>
  - class: mod; gdp-wired stopped on `no clause derives false @step unknown`; given Spacer's invariant: a conjunct gdp-wired can't state here (mod) (38 ms)
- `extra-small-lia/s_multipl_17_000.yml` (906 bytes, 2 Int and 0 Bool slots, 2 predicates)
  - Spacer: LOOPY: <mod>; LOOPX: <mod>
  - class: mod; gdp-wired stopped on `loc is p1 → 3199 <= i0 → 3204 <= i0 @step unknown`; given Spacer's invariant: a conjunct gdp-wired can't state here (mod) (65 ms)
- `extra-small-lia/phases_m_000.yml` (1,038 bytes, 3 Int and 0 Bool slots, 2 predicates)
  - Spacer: inv1: i0 + 1 <= i2; inv1: i1 + 1 <= i2; inv1: <mod>; inv2: i1 <= i0 … (5 clauses in all)
  - class: mod; gdp-wired stopped on `loc is p0 → i1 <= 7 → i0 + i1 <= i2 + 7 @step unknown`; given Spacer's invariant: a conjunct gdp-wired can't state here (mod) (65 ms)
- `extra-small-lia/dillig02_m_000.yml` (1,189 bytes, 6 Int and 0 Bool slots, 2 predicates)
  - Spacer: inv: i4 <= i3; inv: <mod>; inv: i3 <= i4; inv1: i4 <= i3 … (6 clauses in all)
  - class: mod; gdp-wired stopped on `i4 <= i3 @step sat`; given Spacer's invariant: a conjunct gdp-wired can't state here (mod) (65 ms)
- `aeval-benchmarks/multi-phase/s_split_21_000_000.yml` (860 bytes, 4 Int and 0 Bool slots, 2 predicates)
  - Spacer: inv: 0 <= i2; inv: 0 <= i0; inv: <mod>; inv: 9 <= i0 or i0 <= 7 or i2 <= 8 … (23 clauses in all)
  - class: mod; gdp-wired stopped on `i0 <= i2 @step unknown`; given Spacer's invariant: a conjunct gdp-wired can't state here (mod) (76 ms)
- `llreve-bench/smt2/loop__digits10_inl_000_002.yml` (17,400 bytes, 6 Int and 0 Bool slots, 1 predicate)
  - Spacer: INV_MAIN_42: i5 <= i1; INV_MAIN_42: 10·i0 <= i3; INV_MAIN_42: i4 <= i1; INV_MAIN_42: i1 <= i4 + 3 … (16 clauses in all)
  - class: div; gdp-wired stopped on `no clause derives false @step unknown`; given Spacer's invariant: a conjunct gdp-wired can't state here (div) (1,307 ms)
- `eldarica-misc/LIA/llreve/fib_merged_safe.c-1_000.yml` (1,158 bytes, 7 Int and 0 Bool slots, 2 predicates)
  - Spacer: inv_main7: <quantified> or i1 + 2·i3 <= i2 + i4; inv_main7: 2·i1 + 3·i3 <= i2 + 2·i4 or <quantified>; inv_main7: <quantified> or i2 + 2·i4 <= 2·i1 + 3·i3; inv_main7: <quantified> or i2 + i4 <= i1 + 2·i3 … (5 clauses in all)
  - class: quantified; gdp-wired stopped on `2·i6 <= i1 + 3·i5 @step unknown`; given Spacer's invariant: a conjunct gdp-wired can't state here (a quantifier) (73 ms)
- `hcai-bench/arrays_orig/array_fill1_abstracted_000.yml` (1,399 bytes, 4 Int and 0 Bool slots, 4 predicates)
  - Spacer: incr: i1 + 1 <= i0; incr: i1 <= i2 or i2 + 1 <= 0 or i3 <= 42; incr: 42 <= i3 or i1 <= i2 or i2 + 1 <= 0; incr: 42 <= i3 or i1 + 1 <= i2 or i2 + 1 <= i1 … (12 clauses in all)
  - class: quantified; gdp-wired stopped on `i1 <= i2 + 8 @step unknown`; given Spacer's invariant: a conjunct gdp-wired can't state here (a quantifier) (84 ms)
- `eldarica-misc/LIA/llreve/break_safe.c-1_000.yml` (1,965 bytes, 4 Int and 0 Bool slots, 4 predicates)
  - Spacer: inv_main20: i3 <= 10; inv_main20: i1 <= 11; inv_main20: 11 <= i1 or i2 <= i1; inv_main20: 1 <= i3 or 10 <= i1 + i3 … (49 clauses in all)
  - class: quantified; gdp-wired stopped on `loc is p1 → i1 <= i2 @step unknown`; given Spacer's invariant: a conjunct gdp-wired can't state here (a quantifier) (108 ms)
- `eldarica-misc/LIA/llreve/loop2_merged_safe.c-1_000.yml` (2,609 bytes, 5 Int and 0 Bool slots, 5 predicates)
  - Spacer: inv_main15: 2·i3 <= i4; inv_main15: 2·i0 + i4 <= i2 + 2·i3; inv_main15: i4 <= i2; inv_main15: i2 + 2·i3 <= 2·i0 + i4 … (17 clauses in all)
  - class: quantified; gdp-wired stopped on `6·i1 + 2·i4 <= 5·i2 + 6 @step unknown`; given Spacer's invariant: a conjunct gdp-wired can't state here (a quantifier) (135 ms)
- `hcai-bench/svcomp/O3/O3_gcd01_true-unreach-call_true-no-overflow_true-termination_000.yml` (6,028 bytes, 4 Int and 0 Bool slots, 4 predicates)
  - Spacer: main@.lr.ph..lr.ph.split_crit_edge.i: 1 <= i3 or i1 <= i3; main@.lr.ph..lr.ph.split_crit_edge.i: 1 <= i3 or i3 <= i1; main@.lr.ph..lr.ph.split_crit_edge.i: <quantified> or i1 <= i3; main@.lr.ph..lr.ph.split_crit_edge.i: 1 <= i2 or i3 <= i1 … (24 clauses in all)
  - class: quantified; gdp-wired stopped on `i1 <= i3 @step unknown`; given Spacer's invariant: a conjunct gdp-wired can't state here (a quantifier) (664 ms)

## G. Not Lustre, within the templates (16 tasks; 13 proven once given)

Small rules whose invariant is a few bounds and differences, proven at once when given, that the search missed
(`s_split_34`: `-100 <= i0 + i1 <= 100` and bounds; gdp-wired stopped on a candidate of its own). Lacking: the search
alone (which constants the bounds take, which candidate a counterexample picks).

- `aeval-benchmarks/multi-phase/s_split_34_000_000.yml` (758 bytes, 2 Int and 0 Bool slots, 2 predicates)
  - Spacer: inv: 0 <= i0 + 100; inv: 0 <= i0 + i1 + 100; inv: i0 <= 100; inv: i1 <= 1 … (6 clauses in all)
  - class: two values; gdp-wired stopped on `loc is p1 → i1 <= i0 + 63 @step sat`; given Spacer's invariant: proven (1,485 ms)
- `aeval-benchmarks/multi-phase/s_split_37_000_000.yml` (786 bytes, 3 Int and 0 Bool slots, 2 predicates)
  - Spacer: inv: 0 <= i2; inv: 2523 <= i1 + i2 or i0 <= 8; inv: 2023 <= i1 + i2 or i0 <= 6; inv: 523 <= i1 + i2 or i0 <= 0 … (11 clauses in all)
  - class: a disjunction of two (a counterexample's form); gdp-wired stopped on `523·i0 <= 2·i1 + 4·i2 + 4819 @step unknown`; given Spacer's invariant: proven (1,633 ms)
- `eldarica-misc/LIA/reve/023-horn_000.yml` (1,156 bytes, 4 Int and 0 Bool slots, 1 predicate)
  - Spacer: INV1: i3 <= 11; INV1: i3 <= i1 + 1; INV1: i1 <= 11
  - class: two values; gdp-wired stopped on `loc is p0 → 10 <= i1 → i0 + 1 <= 2·i2 @step unknown`; given Spacer's invariant: proven (1,449 ms)
- `eldarica-misc/LIA/reve/026b-horn_000.yml` (1,156 bytes, 4 Int and 0 Bool slots, 1 predicate)
  - Spacer: INV1: i1 <= i0; INV1: i0 <= 11; INV1: i0 <= 10 or i1 + 1 <= i0
  - class: a disjunction of two (a counterexample's form); gdp-wired stopped on `10·i0 <= 9·i1 + i2 + 10 @step unknown`; given Spacer's invariant: proven (2,085 ms)
- `llreve-bench/smt2/clausified/loop__upcount_000_001.yml` (1,252 bytes, 4 Int and 0 Bool slots, 1 predicate)
  - Spacer: INV_MAIN_42: i2 <= i0; INV_MAIN_42: i1 <= i3; INV_MAIN_42: i0 <= i2 + 1; INV_MAIN_42: i0 <= i2 or i1 + 1 <= i3 … (6 clauses in all)
  - class: a disjunction of two (a counterexample's form); gdp-wired stopped on `2·i1 + 5·i2 <= 2·i3 + 5 @step unknown`; given Spacer's invariant: proven (4,218 ms)
- `eldarica-misc/LIA/llreve/break_merged_safe.c-1_000.yml` (1,609 bytes, 3 Int and 0 Bool slots, 3 predicates)
  - Spacer: inv_main11: i1 <= 11; inv_main11: 10 <= i0 + i2 or i2 + 1 <= 0; inv_main11: 10 <= i0 + i2 or 11 <= i1; inv_main11: i0 + i2 <= 9 or i1 <= i0 … (17 clauses in all)
  - class: a disjunction of two (a counterexample's form); gdp-wired stopped on `loc is p0 → i2 <= i0 → 5 <= i1 @step unknown`; given Spacer's invariant: proven (7,998 ms)
- `hcai-bench/svcomp/O0/O0_sum01_true-unreach-call_true-termination_000.yml` (2,271 bytes, 3 Int and 0 Bool slots, 3 predicates)
  - Spacer: main@_bb: i1 + 2 <= 2·i2; main@_bb: 0 <= i1; main@_bb: 2·i2 <= i1 + 2; main@_bb: i1 <= 0 or i1 <= 2·i0
  - class: a disjunction of two (a counterexample's form); gdp-wired stopped on `loc is never p1 @step unknown`; given Spacer's invariant: proven (10,046 ms)
- `llreve-bench/smt2/clausified/loop__while-if_000_001.yml` (2,878 bytes, 5 Int and 0 Bool slots, 3 predicates)
  - Spacer: INV_MAIN_23: 0 <= i2; INV_MAIN_23: i1 <= 0; INV_MAIN_23: i2 <= 0; INV_MAIN_42: i2 <= i0 … (8 clauses in all)
  - class: two values; gdp-wired stopped on `loc is p0 → 0 <= i2 @step unknown`; given Spacer's invariant: proven (12,675 ms)
- `eldarica-misc/LIA/HOLA/04.c_000.yml` (2,928 bytes, 4 Int and 0 Bool slots, 13 predicates)
  - Spacer: h9: 0 <= i2; h9: 1 <= i3 or i2 + 50 <= 0; h3: i3 <= i1; h3: i2 + 50 <= 0 … (33 clauses in all)
  - class: a disjunction of two (a counterexample's form); gdp-wired stopped on `loc is p3 → 0 <= i3 → i1 + 5 <= i2 @step unknown`; given Spacer's invariant: proven (15,977 ms)
- `hcai-bench/svcomp/O3/O3_sum01_true-unreach-call_true-termination_000.yml` (3,196 bytes, 3 Int and 0 Bool slots, 3 predicates)
  - Spacer: main@.lr.ph: i1 + 2 <= 2·i0; main@.lr.ph: i1 + 2 <= 2·i2; main@.lr.ph: 1 <= i0; main@.lr.ph: 2·i2 <= i1 + 2
  - class: two values; gdp-wired stopped on `2·i2 <= i1 + 2 @step unknown`; given Spacer's invariant: proven (17,358 ms)

## H. Unsat, Lustre: short derivations no run finds (273 tasks)

Golem's derivations of false are short (225 of 5 steps or fewer), but each step's request must be a model of a wide
clause condition that leads to the query; gdp-wired's guided runs choose each request one step at a time without the
query in view, and either die after a few steps or wander. Lacking: a model of k steps at once with the query at the
end (a bounded model check over the rule).

- `vmt-chc-benchmarks/lustre/durationThm_3_e1_36_000_001.yml` (2,519 bytes)
  - Golem's derivation: 4 steps; gdp-wired's guided runs: 5720 steps in 509 trials (11.2 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation within the guided runs' depth, its values not found
- `vmt-chc-benchmarks/lustre/durationThm_1_e7_12_000.yml` (2,653 bytes)
  - Golem's derivation: 4 steps; gdp-wired's guided runs: 4191 steps in 322 trials (13.0 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation within the guided runs' depth, its values not found
- `vmt-chc-benchmarks/lustre/durationThm_1_e1_197_000.yml` (2,664 bytes)
  - Golem's derivation: 3 steps; gdp-wired's guided runs: 5672 steps in 364 trials (15.6 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation within the guided runs' depth, its values not found
- `vmt-chc-benchmarks/lustre/car_5_e2_405_e2_1083_000_001.yml` (5,031 bytes)
  - Golem's derivation: 12 steps; gdp-wired's guided runs: 425 steps in 122 trials (3.5 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation longer than the guided runs go (their steps per trial)
- `vmt-chc-benchmarks/lustre/car_6_e2_589_e2_506_000_001.yml` (5,039 bytes)
  - Golem's derivation: 13 steps; gdp-wired's guided runs: 265 steps in 86 trials (3.1 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation longer than the guided runs go (their steps per trial)
- `vmt-chc-benchmarks/lustre/car_4_e3_57_e5_999_000_001.yml` (5,048 bytes)
  - Golem's derivation: 3 steps; gdp-wired's guided runs: 628 steps in 1 trials (628.0 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation within the guided runs' depth, its values not found
- `vmt-chc-benchmarks/lustre/car_3_e1_586_000_001.yml` (5,182 bytes)
  - Golem's derivation: 4 steps; gdp-wired's guided runs: 912 steps in 1 trials (912.0 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation within the guided runs' depth, its values not found
- `vmt-chc-benchmarks/lustre/car_all_e3_1068_000_001.yml` (5,392 bytes)
  - Golem's derivation: 3 steps; gdp-wired's guided runs: 431 steps in 1 trials (431.0 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation within the guided runs' depth, its values not found
- `vmt-chc-benchmarks/lustre/PRODUCER_CONSUMMER_luke_1_000_001.yml` (6,268 bytes)
  - Golem's derivation: 3 steps; gdp-wired's guided runs: 285 steps in 4 trials (71.2 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation within the guided runs' depth, its values not found
- `vmt-chc-benchmarks/lustre/car_5_e3_11_000.yml` (5,099 bytes)
  - Golem's derivation: 12 steps; gdp-wired's guided runs: 646 steps in 1 trials (646.0 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation within the guided runs' depth, its values not found

## I. Unsat, the others (30 tasks)

`hcai-bench/svcomp`, `reve` and `rust-horn` programs with a reachable error a few branches deep, and two counting to
10,000. Lacking: the bounded model check of H across branches, and for `s_split_01`/`s_split_48` (10,002 steps) a
derivation that summarizes a loop (acceleration).

- `aeval-unsafe/s_split_01_000_001.yml` (536 bytes)
  - Golem's derivation: 10002 steps; gdp-wired's guided runs: 127051 steps in 64 trials (1985.2 a trial); stopped: unknown: a candidate's step goal refuted at a state no candidate rules out (sat)
  - class: a derivation past 2,000 steps (a guided run's cap)
- `aeval-unsafe/s_split_48_000_001.yml` (671 bytes)
  - Golem's derivation: 10002 steps; gdp-wired's guided runs: 121605 steps in 61 trials (1993.5 a trial); stopped: unknown: a candidate's step goal refuted at a state no candidate rules out (sat)
  - class: a derivation past 2,000 steps (a guided run's cap)
- `hcai-bench/svcomp/O0/O0_terminator_01_false-unreach-call_true-termination_000.yml` (1,634 bytes)
  - Golem's derivation: 4 steps; gdp-wired's guided runs: 865 steps in 99 trials (8.7 a trial); stopped: unknown: a candidate's step goal refuted at a state no candidate rules out (sat)
  - class: a derivation within the guided runs' depth, its values not found
- `hcai-bench/svcomp/O3/O3_nec20_false-unreach-call_true-termination_000.yml` (1,991 bytes)
  - Golem's derivation: 4 steps; gdp-wired's guided runs: 1560 steps in 284 trials (5.5 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation within the guided runs' depth, its values not found
- `hcai-bench/svcomp/O0/O0_nec20_false-unreach-call_true-termination_000.yml` (2,110 bytes)
  - Golem's derivation: 5 steps; gdp-wired's guided runs: 382 steps in 79 trials (4.8 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation longer than the guided runs go (their steps per trial)
- `rust-horn/bmc-2-test-bmc-2-unsafe_000.yml` (2,187 bytes)
  - Golem's derivation: 7 steps; gdp-wired's guided runs: 23925 steps in 8651 trials (2.8 a trial); stopped: unknown: the law's step goal refuted at a state no candidate rules out (sat)
  - class: a derivation longer than the guided runs go (their steps per trial)
- `hcai-bench/svcomp/O0/O0_sum01_bug02_false-unreach-call_true-termination_000.yml` (2,517 bytes)
  - Golem's derivation: 10 steps; gdp-wired's guided runs: 251 steps in 125 trials (2.0 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation longer than the guided runs go (their steps per trial)
- `hcai-bench/svcomp/O0/O0_sum01_false-unreach-call_true-termination_000.yml` (2,271 bytes)
  - Golem's derivation: 14 steps; gdp-wired's guided runs: 235 steps in 113 trials (2.1 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation longer than the guided runs go (their steps per trial)
- `hcai-bench/svcomp/O3/O3_id_o3_false-unreach-call_000.yml` (2,452 bytes)
  - Golem's derivation: 6 steps; gdp-wired's guided runs: 1032 steps in 223 trials (4.6 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation longer than the guided runs go (their steps per trial)
- `hcai-bench/svcomp/O3/O3_id_o10_false-unreach-call_000.yml` (2,453 bytes)
  - Golem's derivation: 13 steps; gdp-wired's guided runs: 1339 steps in 287 trials (4.7 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation longer than the guided runs go (their steps per trial)
- `hcai-bench/svcomp/O3/O3_id_o100_false-unreach-call_000.yml` (2,454 bytes)
  - Golem's derivation: 103 steps; gdp-wired's guided runs: 885 steps in 192 trials (4.6 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation longer than the guided runs go (their steps per trial)
- `hcai-bench/svcomp/O3/O3_id_o1000_false-unreach-call_000.yml` (2,455 bytes)
  - Golem's derivation: 1003 steps; gdp-wired's guided runs: 1018 steps in 219 trials (4.6 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation longer than the guided runs go (their steps per trial)
- `llreve-bench/smt2/clausified/faulty__barthe!_000_001.yml` (2,661 bytes)
  - Golem's derivation: 14 steps; gdp-wired's guided runs: 7177 steps in 6685 trials (1.1 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation longer than the guided runs go (their steps per trial)
- `eldarica-misc/LIA/reve/003c-horn_000.yml` (3,232 bytes)
  - Golem's derivation: 14 steps; gdp-wired's guided runs: 11205 steps in 10628 trials (1.1 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation longer than the guided runs go (their steps per trial)
- `eldarica-misc/LIA/reve/025c-horn_000.yml` (4,329 bytes)
  - Golem's derivation: 8 steps; gdp-wired's guided runs: 14156 steps in 2916 trials (4.9 a trial); stopped: unknown: a candidate's step goal undecided (unknown)
  - class: a derivation longer than the guided runs go (their steps per trial)
