# CHC-COMP's ADT-LIA track through gdp-wired

This directory runs CHC-COMP 2026's ADT-LIA tasks: Horn clauses over algebraic datatypes and linear integers, 1,131 of
them (`chc-comp/chc-comp26-benchmarks` at `b4fa7a7`, `ADT-LIA.set`). Spacer (Z3 5.3.1) and Eldarica 2.3 run beside
it. Golem reads no datatypes.

| File | What |
| --- | --- |
| `horn.ts` | The task read: compare/chc's clause reader (`parseHorn`) and TIP's datatypes (tip.ts). Then the model guessed, each clause made a TIP goal over it (`lawOf`), and a derivation found and checked (`deriveQuery`, `checkDerivation`) |
| `solve.ts` | One task: every law through compare/tip/translate.ts and proveData; answers sat, unsat, unknown or unsupported |
| `modal_adt.py` | The track on Modal: each task in its own container (2 vCPU, 4 GB), each tool under the same 60 s limit, as compare/chc/modal_chc.py does |
| `pilot.json` | The fixed pilot: 48 tasks, stratified by family and verdict, drawn by the SHA-1 of the task's path from the tasks some CHC-COMP'26 entrant decided |

    modal run compare/chc-adt/modal_adt.py --out runs/adt/<name> [--tools gdp,z3,eldarica] [--tasks pilot|all]
    bun compare/chc/summary.ts runs/adt/<name>

## The idea: a Horn system over datatypes is a program written as relations

Almost every task of the track is a functional program put into relations: `len(cons(h, t), n + 1) ← len(t, n)`,
`ff ← len(xs, a) ∧ len(ys, b) ∧ len(xs ++ ys, c) ∧ c ≠ a + b`. A satisfying assignment is a model, so the model is
read back as that program, and every clause becomes a theorem about it. One engine answers both TIP's induction
problems and this track's invariants: core/data.ts's lemma search, schemes and measures, through compare/tip's
translation.

- **The model.**
  - Each predicate is read by a mode: the argument its function computes from the others, a Bool function of all of
    them, or false (one read only on the way to false, such as the formatter's `ff`).
  - Each clause is normalized: its datatype equations are solved by unification, with constructors free and trees
    finite.
  - Each clause is scheduled from its head's inputs: definitions, guards, calls, and a call's result matched against a
    pattern. Its function is the clauses' patterns compiled into matches.
  - The Int arguments that every fact has nonnegative (a greatest fixpoint, the size law of TIP's naturals written as
    Int) guard the function and its calls. A functional model is its graph on that domain.
  - Arguments no function reads are dropped. A call's key is the pairing of its arguments, whose degree doubles with
    each one.
  - An assignment of modes is chosen by cost: a default case 1, a Bool function 20, an overlap of different values 100,
    false 1,000. Each group takes its cheapest given its callees', then changes are made one group at a time. A caller
    may need a callee's other reading (drop's `minus(C, G, 1)` needs C = G − 1).
- **Sat.**
  - Every clause is a TIP goal: ∀ vars. body ⇒ head, each application replaced by its reading.
  - A defining clause is stated in the variables its function computes, so the unfolded body reads the hypotheses'
    terms.
  - Each goal is proven by proveData, its cyclic proof checked by the kernel, its functions' termination proven. Every
    clause proven means the program is a model.
  - The model is a guess, never trusted: a wrong reading is a law that isn't proven.
- **Unsat.** A query's counterexample (proveData's refutation) is derived clause by clause, and the derivation is
  checked against the clauses as written, with tip.ts's evaluator and no gdp-wired code.
- **Refused, with the reason:** a sort that isn't Int, Bool or a declared non-parametric datatype, and a system that no
  reading runs.

What became shared:
- core/data.ts's termination and recursion schemes read Int parameters (`toNat`, Lean's Int.toNat) and a condition's
  choice on Bool as an if.
- core/transfer.ts bridges a Bool function of two values of one datatype that is = or ≠ (the encodings' `diseq`).
- compare/chc's reader takes its sorts (`parseHorn`).
- compare/tip's translation reads Int as the integers on request.

## The pilot (60 s, Modal, one run each; runs/adt/ in this checkout)

| tool | solved | sat | unsat | wrong |
| --- | --- | --- | --- | --- |
| gdp-wired (p6, bfbef7b) | 14 | 8 | 6 | 0 |
| Spacer | 13 | 5 | 8 | 0 |
| Eldarica | 14 | 7 | 7 | 0 |

Eight of gdp-wired's 14 are solved by neither rival here: the four weird_nat_add3* tasks, isaplanner/prop_56,
prod/prop_04 and prod/prop_20 (sat), and false/regexp_deluxe_switcheroo (unsat). By run: p1 10, p2 12 (the equality bridge), p3 13 (Int measures), p4 14 (Bool
conditions as paths, queries tried first).

Why the rest miss (p4's 34; p6 the same in kind):
- About 12 queries the lemma search doesn't prove. Most of them are TIP theorems over naturals written as Int (clam's
  `drop B (drop C D) = drop C (drop B D)`, B and C Int with B, C ≥ 0).
- 8 defining clauses not proven. Some run out of memory: an Int argument's code in a call's paired key grows the
  unfolded term about 16-fold per unfolding (rotate: 40 M characters at the third).
- 4 terminations not proven: a nested call (bubble), div, fibo's ring, the hotel tasks.
- 2 readings that are wrong (refuted).
- rust-horn and adt-purified: prophecy encodings (`~ret` of a `~Mut`, existential in a clause), whose refutations
  aren't derivations.

## CHC-COMP'26's own results (chc-comp.github.io/chc-comp-2026/tables, 1,131 tasks)

| tool | score | wrong |
| --- | --- | --- |
| Choco Catalia | 482 | 0 |
| Spacer (hors concours) | 389 | 1 |
| Eldarica | 240 | 0 |
| PCSat | 230 | 0 |
| MuCyc | 73 | 13 |

Choco Catalia, a catamorphism-based abstraction, was the winner.

## What the full track would take in the bar

1. A `adt` group in gates/bar.ts launching `python3 compare/chc-adt/modal_adt.py`. That needs `run(ex, …)` and
   `fanout.cli` as modal_chc.py has them (its shard and run could take the set and the command instead of being
   copied).
2. A dev set of about 120 tasks, from a baseline of three runs.
3. The rivals once per benchmark commit (cached).

Spend, from this pilot's bill:
- gdp-wired alone about $0.07 per 48 tasks, so about $1.65 a run of the 1,131 and about $5 for a three-run baseline;
- Spacer and Eldarica about $0.19 per 48, about $4.4 once.

Before that is worth it:
- recover TIP's naturals from Int (the nonnegative positions as a Peano datatype in the program, read as naturals by
  translate.ts: the lemma search's own ground);
- keep an Int argument's code out of a call's key.
