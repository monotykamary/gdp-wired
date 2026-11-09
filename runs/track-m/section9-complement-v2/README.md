# T-9A — named complement generator gap; stop

**Stop before T-9B/C/D or implementation.** The exact branch is:

```
Inv* @step, op = 5
 a$# = i
 j$ < i
 CT[i] < CfgT[j$]       // complement of G = CfgT[j$] <= CT[i]
```

This is the original 24-cut, 32-candidate restricted T-A packet, with the
original 24 path atoms retained and the complement added. Hash:
`78b51495639d2e70ecdb871465c3d59c7cdfbc43e0abcf2804ab6b251f76f5c3`.
All source queries use the live closure's own `source()` slices. No source model
is reused, and no path/count atom is discarded for a fresh-process approximation.

## Three A/B interleaved repeats

Same exclusive **bx_3kjzmmhv**, eight pinned vCPUs. A is the bare-leaf control;
B is a separate complement-only diagnostic, not the failed two-branch test.

| Mode | Counted units (all three identical) | Probe wall median | Probe wall max |
|---|---:|---:|---:|
| A: bare leaf | 226.582788 | 0.171 s | 0.187 s |
| B: complement alone | **227.664816** | **0.141 s** | **0.144 s** |

The full packet-regeneration processes have median/max walls **9.858 / 11.527 s**
for A and **10.261 / 10.563 s** for B. Probe work/walls exclude regeneration.
The separate B run keeps its own prescribed 400-unit diagnostic ceiling. It
is not combined with the earlier G branch to claim a 400-unit two-child proof.

In every complement repeat, the numeric query returns a validated model with
V = **{27, 32, 77, 84}**. Every candidate returns a validated source SAT model:

| Original candidate | Outcome | Counted units, each repeat |
|---|---|---:|
| 84 | SAT | 37.042698 |
| 77 | SAT | 15.475372 |
| **27** | **SAT** | **27.602556** |
| **32** | **SAT** | **21.179086** |

No new cut is admitted. Thus the requested condition holds: 27 and 32 are SAT
on the complement too. The model-driven loop has exhausted the violated pool
at this scope. This is a **generator gap for this captured restricted proof
pool**, not a proof that the full production pool has no useful fact, and not
a protocol counterexample.

## Concrete valuations

The numeric model includes `op=5`, `i=a$#=1`, `j$=0`, `size=2`,
`CT[i]=CfgT[i]=0`, `CfgT[j$]=1`, `?all$1=?all$3=1`, `?all$2=0`.
The source models also set `St[j$]=0`. They are separate valuations: candidate
27 uses `i=a$#=63`, `j$=61`, `size=64`, while candidate 32 uses `i=a$#=1`,
`j$=0`, `size=2`; both have `CT[i]=0 < CfgT[j$]=1`. They are not spliced into a
single purported protocol state. Full models, exact source ASTs and paths are
in **generator-gap.json** and **B1.json–B3.json**.

The strict two-branch test remains failed; see `../section9-ta-v3/README.md`.
No later Section 9 test, production implementation, default change, cap /
allowance increase, trusted-rule change, or Gate 1 rerun is authorized by this
result. The first complement attempt failed a static check before measurement.
