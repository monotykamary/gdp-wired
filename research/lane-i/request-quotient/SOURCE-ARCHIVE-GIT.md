# Source archive / Git identity supplement

After recovering the original bundles, this read-only command was run in I:

```
git archive bfe647cfd3b81e10c497ca4d5911a8097a02586b | sha256sum
```

Observed SHA256:
`7d4506ba760d1811d7bedb4de4790fe1f03ad3508688e5fdad85f16d500314e0`.
This is byte-identical to the recovered census source.tar and the source.tar
used by the strict Q1 rerun. It binds that source archive to the immutable Git
commit, without any old producer, proof, census or timing rerun.

This supplement does not attest a loaded process, toolchain binary, every
transitive dependency or vendor provenance. D's separately accepted recovered
archive comparison and original vendor manifests remain distinct evidence.

New strict input bundles are retained at:
`runs/lane-i/quotient-input-custody/bundles/{strict-q1,strict-types}/`.
Their complete top-level file hash manifests are `strict-q1-INPUT.sha256` and
`strict-types-INPUT.sha256`; the Q1 implementation hashes are
`strict-DRIVERS.sha256`. Old accepted auditor and receipt bytes are unchanged.
