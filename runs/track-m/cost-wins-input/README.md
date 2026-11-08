# Exact A/B baseline input

`baseline.tar.gz` is a `git archive` of commit **50109a36** containing core,
kernel, lean-kernel, interchange, research and the pinned package/config files.
`baseline.commit` retains the full commit ID and `archive.sha256` its archive
digest. The remote runner shares the same installed dependencies and vendor
pins between this baseline and the working-tree candidate.

The existing `research/track-m/profile-family.ts` and every kernel source are
compared byte-for-byte before any measurements. The new wrapper only adds
cache counter snapshots after each timed law result.
