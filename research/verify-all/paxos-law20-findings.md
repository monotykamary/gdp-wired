# Paxos law 20: exact-context tree/row localization

## Verdict

**Resolved locally: a valid Boolean-derived contradiction row is not translated into a row derivation supported by the Lean mirror. No invalid TypeScript arithmetic/tree step was found at the rejected nodes.** The emitter preserves the meaning of the singleton disjunction but drops its wrapper. TypeScript `facts` can replace a false singleton disjunction by the derived row `1 ≤ 0`; Lean `facts` of the emitted bare atom instead supplies the atom's ordinary arithmetic row. The exporter nevertheless claims the TypeScript constant row unchanged. Lean correctly refuses that row claim.

This is a **proof-translation/completeness defect (valid-but-unexported rule)**, not demonstrated semantic misencoding of the hypotheses and not demonstrated unsoundness of TypeScript. It is narrower than saying simply “the emitter has wrong arithmetic.” The hypotheses plus exact inherited path really are inconsistent: kernel-checked local refutations and a semantic theorem establish this. No false-law mutant is warranted by this finding.

The original retained Paxos proof remains rejected. A separately named diagnostic replacement of two leaves passes `checkT`; that replacement is **not the original certificate, not a new Paxos safety theorem, and not a repair to production code**. Law 12 and whole-machine admission are outside this part (b).

## Inputs and scope

Repository/branch: `gdp-wired-verifyP`, `claude/verify-all`, HEAD `e11165280a1bab4944a692a64ab1554e5f53c82e`.

Original archive: `runs/verify-all/capture-all/capture-paxos_epr.log`, `ARCHIVE_BEGIN` base64 xz tar.

- Packet SHA-256: `dc0e230fab5d0081a2c9d4f56b525ef314a2e78780647d3cb2fafaf3a512f386`.
- Original emitted Lean SHA-256: `e31b4c24e46e021c0b0187d1c2b71736530c16e47db15c18eb4d8cd77cfc15b1`.
- Law: zero-based index **20**, `carry:co-write:6282256ba10ee781 @step`.
- No lemma cuts. `checkMC` is true in TypeScript. Exact reconstructed full hypotheses equal the directly encoded TypeScript hypotheses (reconfirmed by kernel reduction).

Read `paxos-diagnostic.md`, `paxos-diagnostic.ts`, `check-lean.sh`, and unchanged relevant `kernel/kernel.ts`, `core/check.ts`, `lean-kernel/emit.ts`, `lean-kernel/Kernel.lean`, `Cert.lean`, and `Count.lean`. All extraction, program checks, probes, and Lean checks ran on boat using `supercomputer`; laptop operations were reads/edits, git/status, scheduling, and small receipt hashes. No external solver, cache deletion, cleanup, production edits, branch/worktree changes, commit, or push.

## Exact localization and original node data

Routes below start at the retained step-tree root; **Y** is `.yes`, **N** is `.no`. The traversal order is depth-first, Y before N. “First rejected node” means the first failing leaf after descending failing ancestors; root and ancestors fail because their conjunction includes it, not because splitting itself is refused.

TypeScript checked **all 73 nodes, including all 37 leaves**, using the original complete goal and the exact accumulated `Map` path. All returned true. Lean traversed the **original emitted** `law20k.tree`, `law20k.tab`, and full `law20hs`, extending its original newest-first path list at every split. Its complete nontruncated `LEAN_BAD_LEAVES` output is:

```text
[[true,true,true,true,false], [false]]
```

Thus only leaves **YYYYN** and **N** reject; the other 35 leaves accept. By the unchanged conjunction definition of `checkT`, the rejecting node routes are root, Y, YY, YYY, YYYY, YYYYN, and N. The terminal diagnostic also computes all 73 original Lean node results; the default Lean pretty-printer truncates the long all-node display, so use the complete short bad-leaf output and the structural `checkT` definition rather than treating the printed long list as a complete serialization. The exact TS path/node/base-row JSON and original Lean definitions are preserved in each raw archive.

### First failing leaf: YYYYN

Exact inherited TS atoms in insertion order (all full hypotheses retained):

| Split | Linear row | Branch |
|---|---|---|
| 1 | `carryKeyX - 63` | true (`≤ 0`) |
| 2 | `Left[n:64,r:1] - 1` | true |
| 3 | `Left[carryKey:1,carryKeyXX#:64] - 1` | true |
| 4 | `carryKey - carryKeyX + 1` | true |
| 5 | `carryKeyXX# - size + 1` | false (`≥ 1`) |

The two `Left[...]` names are literal canonical TS column names, not a new interpretation of the map keys. Lean inherits these same decisions newest-first. The fifth row has original Lean coefficients `[(1,-1),(62,1)]`, constant `1`.

Original TS leaf and its referenced row:

```json
{"leaf":[{"kind":"input","index":23}]}
{"lin":{"1":1},"label":"","src":{"fact":24}}
```

The emitter compacts the selected row to index 0:

```lean
.leafAt [(lconst 1, .fact 24)] [.input 0] [] []
```

Terminal decomposition: row admission **false**, arithmetic `Cert.check` on the claimed row **true**, missing rows `[(0, {coefs := [], const := 1})]`. Hence there is no cut/combine discrepancy here: the only original arithmetic step inputs a claimed constant contradiction.

### Second failing leaf: N

The only inherited split is `carryKeyX - 63`, false. Original TS leaf is `{"leaf":[{"kind":"input","index":20}]}`; row 20 is again `{"lin":{"1":1},"src":{"fact":24}}`. The emitted leaf has the same compact one-row/one-input form. Hypothesis 24 contains the other relevant singleton disjunction, `or [carryKeyX < 64]`.

## Why the constant contradiction is sound but not admitted

At YYYYN, full hypothesis 24 contains positively required:

```text
or [carryKeyXX# < size]
```

This occurs in the positive conjunction obtained through the surrounding negation/disjunction structure. At N the corresponding required component is `or [carryKeyX < 64]`. The whole hypothesis is retained; no detached-subtree test substitutes a different hypothesis for it.

- `kernel/kernel.ts` `facts`, lines 328–332: for positive `or`, filter disjuncts already known false. With no open disjuncts, return `[k(1)]`.
- For the contained bare `<` atom, TS returns the arithmetic comparison row, not that constant row.
- `lean-kernel/emit.ts:618` reduces n-ary connectives with `reduceRight` and no initial value. A singleton `or` is emitted as the atom itself.
- `lean-kernel/Kernel.lean:1341–1377` computes facts of the emitted atom. In particular, a positive `.lt` returns its arithmetic row; it does not replace that row by `1` just because the path contradicts it.
- `Kernel.lean:1590–1596` `leafAtOk` demands the claimed row be present in its hinted source or full computed rows. Mathematical derivability alone is insufficient; the certificate must contain its derivation.

For YYYYN write `a = carryKeyXX#`, `b = size`. Hypothesis 24 entails `a < b`, while the last false split means `a - b + 1 ≥ 1`, hence `a ≥ b`. They cannot both hold. Equivalently the two admitted rows are

```text
r       = a - b + 1 ≤ 0       (from hypothesis 24)
flip(r) = b - a     ≤ 0       (from the inherited false split)
-------------------------------------------------------------
          1         ≤ 0       (sum, positive multipliers 1 and 1)
```

At N the analogous rows are `carryKeyX - 63 ≤ 0` and `64 - carryKeyX ≤ 0`, again summing to `1 ≤ 0`.

**This answers the mathematical invalidity question: the alleged invalid row is valid under its real context.** There is no satisfying local valuation to exhibit. Singleton elimination is semantically correct, but it changes what `facts` returns syntactically and therefore what the retained leaf is allowed to claim without additional steps.

## Kernel proofs, tiny probe, and diagnostic modification

### 1. Original failure, unchanged

The terminal generated `validate.lean` proves with ordinary kernel `decide`:

- `first_original_rejected`: original YYYYN node checked with full original hypotheses and inherited path is false.
- `root_no_original_rejected`: original N node checked likewise is false.

The original failed `theorem verified_check` is not imported. Scripts copy only the preceding retained definitions into separate files; original packet and original Lean hashes are asserted first.

### 2. New local arithmetic fragments and semantic theorem

`first_source_refutation` and `root_no_source_refutation` prove that the following **new**, explicitly separate three-step fragment checks with **only hypothesis 24** and the **entire original inherited path**:

```lean
.leafAt [(r, .fact 0), (flip r, .atom 0)]
  [.input 0, .input 1, .combine 0 1 1 1] [] []
```

The smaller hypothesis list is only a strengthening control: original failures were first checked with full hypotheses. In this control `.fact 0` deliberately names the single retained source hypothesis; `.atom 0` names the newest original split. `first_source_inconsistent` applies unchanged `checkT_sound` to prove that **any** `Model` satisfying hypothesis 24 and that exact original path yields `False`. It is a semantic theorem, not just differing checker return values.

### 3. Tiny serialized probe and non-triggering/corrected controls

`paxos-law20-validate.ts` constructs and JSON round-trips finite proof data:

```text
goal = [or [x < y], not (x < y)]
split = x - y + 1
yes leaf = input 2
no  leaf = input 1
```

This is an **unsatisfiable synthetic goal**, not a false machine law. The hand-supplied tree is accepted by TS; its ordinary emitter output is rejected by Lean. Replacing `or [x < y]` by the semantically equivalent bare `x < y` in TS is a non-triggering control: that same hand-supplied tree is rejected.

`research/verify-all/paxos-law20-semantic.lean` proves the emitted tiny failure, acceptance of a separately corrected tiny tree with the two-row sum at its N leaf, and `tiny_unsatisfiable` using unchanged `Kern.sound`. It also proves singleton-disjunction semantic equivalence and the generic arithmetic contradiction. No automatic `proveRule` or proof search was run; these are explicitly hand-supplied probe/control certificates. Because the localized TS rule is sound, no false-law mutant or interpreter counterexample is claimed.

### 4. Diagnostic adapted full tree, not original

`diagnosticAdaptedTree` copies the retained tree and replaces **only** YYYYN and N with the two-row/three-step fragment above, preserving the original table, all hypotheses, every split, and all other leaves. The original `law20tree` stays unchanged. Kernel reduction prints `("ADAPTED_TREE_CONTROL", true)` for `checkT` of this distinct tree. This is a diagnostic confirmation of the isolated cause, not a replacement certificate sold as original or a whole-machine verification.

## Reproduction and terminal receipts

All jobs: `cpu:4`, `memory:14336`, `timeout:1800`, `vm_type:large`; Lean subprocess bounded by existing `check-lean.sh`. These are diagnostics, not benchmark claims. Use job `summary.tsv`, not the outer scheduler client's exit code.

```sh
supercomputer run --jobs research/verify-all/paxos-law20-localize.jobs.json --out runs/verify-all/paxos-law20-localize --class interactive --data runs/verify-all/capture-all:evidence
supercomputer run --jobs research/verify-all/paxos-law20-deep.jobs.json --out runs/verify-all/paxos-law20-deep --class interactive --data runs/verify-all/capture-all:evidence
supercomputer run --jobs research/verify-all/paxos-law20-validate.jobs.json --out runs/verify-all/paxos-law20-validate --class interactive --data runs/verify-all/capture-all:evidence
supercomputer run --jobs research/verify-all/paxos-law20-validate.jobs.json --out runs/verify-all/paxos-law20-terminal --class interactive --data runs/verify-all/capture-all:evidence
```

| Output suffix | Boat batch | Job exit | Seconds | Result |
|---|---|---:|---:|---|
| `paxos-law20-localize` | `20261109-093033-xtbxy9` | 0 | 24.91 | exact-context first/both rejected leaves |
| `paxos-law20-deep` | `20261109-093208-k7704p` | 1 | 48.63 | diagnostic `Inhabited C` indexing error; source/component data useful, not a clean proof receipt |
| `paxos-law20-validate` | `20261109-093924-0tl5iz` | 1 | 26.49 | tiny semantic/control proofs pass; local semantic theorem tactic malformed (`sorryAx`), excluded as final evidence |
| `paxos-law20-terminal` | `20261109-094145-xe661l` | 0 | 33.98 | all files check; no elaboration error or `sorryAx`; final evidence |

The two failed attempts are preserved, not silently overwritten. Each job archives its exact generated Lean/data inside `RAW_ARCHIVE_BEGIN` / `RAW_ARCHIVE_END` in its own log (base64 xz tar). The script changed to fix the local theorem between validate and terminal; their generated-file hashes below distinguish them. No failed theorem is used as evidence.

The final job checked, in order:

1. `research/verify-all/paxos-law20-semantic.lean` — `LEAN_WALL seconds=0.28 maxrss_kb=495476 exit=0`.
2. `runs/verify-all/paxos-law20-work/tiny-emitted.lean` — `seconds=0.26 maxrss_kb=489276 exit=0`.
3. `runs/verify-all/paxos-law20-work/validate.lean` — `seconds=26.51 maxrss_kb=1666740 exit=0`.

Lean: 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. All proofs use kernel-checkable `decide`, ordinary tactics or existing soundness theorems; no `native_decide`, added axioms, or placeholders. Printed dependency lists contain only Lean's pre-existing `propext`, `Classical.choice`, and `Quot.sound` (some elementary proofs need a subset).

### SHA-256 anchors

| Artifact | SHA-256 |
|---|---|
| `paxos-law20-localize.ts` | `a3d10f78b4b62d0f719cdce57c2907c63c92ef9c977f4bac03dd68e6957617c5` |
| `paxos-law20-localize.jobs.json` | `6c5535506a029627b7d149896adbbf7f10b07c2a4a71964307cc1ca0d4693ef2` |
| `paxos-law20-deep.ts` | `b4e3111edc5eb15aa15703e683b08f4356725c54460b97577c1f5da30ca2e195` |
| `paxos-law20-deep.jobs.json` | `8b7a47a01c60e2128d1b1bfa3ac447b9953602500c30226e7c671a1ea86bce2d` |
| `paxos-law20-semantic.lean` | `023faefa269d96f87803d2fae02f3c8033b354bd1cdd4eaad798f62cbf7b2f7e` |
| final `paxos-law20-validate.ts` | `a192a24a6fea959f8896d777dbf2cf397311a1bd0ed5eccda42b7fd886f153a3` |
| `paxos-law20-validate.jobs.json` | `3a1e4ee14ff009bc257a268821e0198aaa8dd9807eb0639bd4ad0b579c738cf3` |
| generated `localize.lean` | `498d2017d0377da3dbacc205ebe2c8d8107e8f10d308e23f099b8f393ac3f28d` |
| failed generated `deep.lean` | `2a1886070b651ea1ffc8b4513b6fb039a264a88abf809089a01a3a6030e70087` |
| failed generated `validate.lean` | `22458eebc9d60dad252d585f55bbb9e3cdea2309c334d25dd2cd6c1b061bb979` |
| final generated `validate.lean` | `3d47991d66529c90181efd31fe6165307164a2cf64e04e90978c41a1ef262966` |
| generated `tiny-emitted.lean` | `780a52a754c4454d2197a585e0bec30d87668c47d5460d472f15d4ceef6985dd` |
| localization log | `b4814ce26d7202ed84726da21e9a37a6547e90e9235beeb2358d7cd705b16537` |
| deep log | `97a157af984c277aeae0c0b4fe32cf47acda21b76893d12489e4bdb43eea3156` |
| failed validate log | `f190542225cd5e3e837c12e86616d422f43451073aec4b8cd5e63745ac9a82d2` |
| final terminal log | `17ce685be65380ae37a1b086168b8e6017bf4773f742a417e8b41b38af4aa5e1` |
| final `summary.tsv` | `e807c7eee97cca08d88416f559658d79b65e7a16218af44683efeaaef4469f06` |

## Limits and handoff

The arithmetic-vs-hypotheses dichotomy was too narrow: full hypotheses are identical, and the arithmetic is valid, but semantically equivalent connective normalization changes row-extraction completeness. The local cause is established, not left as an unresolved wall. No universal TS soundness assertion follows, and the other 27 accepted families do not cover this failing feature merely because they passed (Main owns the feature census).

All four owned boat jobs and their local scheduler clients are terminal. No process was killed; no extra waiter remains. A bounded waiter timeout and a failed waiter wrapper occurred during the deep job, but neither restarted nor cancelled it; its terminal receipt was collected. The failed wrapper performed no repo mutation. New files are exclusively `research/verify-all/paxos-law20-*`; raw job outputs exclusively `runs/verify-all/paxos-law20-*`. Other agents' files are untouched. Main owns integration, final report, and any commit.
