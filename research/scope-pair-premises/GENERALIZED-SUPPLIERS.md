# Generalized supplier closure (successor of 85a)

Authority: Main's whole-class decision replaces the limitation-only plan. The 85a pair-only code/result remains an immutable reference, not B's composition target.

## Closed row-kind coverage

| Native row source | Availability dependency retained |
|---|---|
| `atom` | Fixed native path/cut prefix; no fabricated fact owner |
| `fact:i` | Hypothesis i, plus all legacy references |
| `pair:[p,q]` | Both initial cell names; every root owner and transitive introduction ancestor is conservatively retained |
| `term:t` | Generating name t, even when absent/cancelled in that row's coefficients; all root ancestors of t |
| `nat:n` | Full-closure name n, including names introduced only by other term rows; all root ancestors |
| certificate square | Present in the unchanged certificate; no hypothesis needed to create it |
| certificate product | Both referenced operands, recursively, with original square offsets |

Only atom/fact rows seed roots. Term rows add introduction edges; pair rows do not invent a new name and naturality rows do not seed themselves. Root-name collection includes zero entries, all variable/cell/term/monomial names, and duplicate fact suppliers. Multi-source reverse reachability computes the same root-owner union as forward transitive propagation. The original source rows are used, not a guessed expression decomposition or only nonzero coefficients.

## Superset and failure boundaries

The result always starts with `countedCertificateHyps`. For valid native rows the new graph retains every initial pair-cell owner retained by 85a, plus generated term/nat provenance. It can keep extra owners; it never replaces successful old dependencies with fewer. Incompatible declared premises still refuse. The code keeps original R1 exception propagation and all existing checkers/transport logic.

Budget/time exhaustion is not an ordinary missing-premise result. The source-tag union is checked; an unsupported row source declines rather than inventing provenance. Native fixed-path determinism and ordinary valid certificates are assumptions of the availability argument. This is not a claim that arbitrary source/target transformations must transport.

## New tenth test

Direct: H0 x<0, H1 min(x,y)<=100, t=min(x,y). Native H0 + (t-x) + (-t) gives 1<=0. H1 is not cited as a fact but introduces t. The old hypothesis set is [0], whose exact reduced transport declines; the new set [0,1] transports and passes native checking.

Transitive subcase: H1 min(min(x,y),z)<=100 introduces outer u. Only its generated row introduces inner t; the proof still uses t-x and -t. New collection must walk t->u->H1. The control asserts no original H1 fact coefficient contains t, so retaining H1 cannot be mistaken for direct-name lookup.

Both are within one new test; the original nine remain. Actual outcomes are recorded only after Main's separate one-shot generalized check. No historical T301/S51 proof result is inferred from a synthetic control.
