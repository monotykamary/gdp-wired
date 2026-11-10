# Next candidate after d3adf3c9

Baseline for the next official gate: `8214a543bc44e88d979f9e4457d7370e7e3c122b`.
This checklist is not a gate pass.

## Generic completeness repair

The replacement at `kernel/prove.ts:1237` was introduced by `1be4ffc1`
(Lane B's arithmetic-boundary/model-value change). A `Map<number,E>` was
rewritten to constants when a boundary existed, losing equal-valued symbolic
terms. Commit `bed9ecb3` retains the original symbolic domain and adds distinct
constant terms. Tuple and evaluation limits are unchanged. The new test in
`kernel/model-values.test.ts` transcribes Lane D's symbolic-binder case: a
symbolic instance must prove, a constant-only instance must not, and the
helper must retain both. The previous constant-alias regression still requires
the constant witness as well as the newly retained symbolic one.

## Core/kernel test roster

Commit `985890c1` adds all 21 new omitted files from Lane D's audit, plus the
inherited `core/extract-sol.test.ts` hole. Recursive filesystem coverage is
checked before listing or running any shard. Explicit long-suite `bun test`
commands account for the 22 inherited long-only files; no blanket exemption
for old files exists. Unknown files, nonexistent entries and duplicate quick
entries fail. Coverage tests include a new nested file and a missing-file
negative control. Solidity tests may explicitly skip when tools are absent;
a scheduled file is not a claim that optional toolchains executed.

## Original IC3Syn models, not an equivalence assertion

The P* change came from Track M / Lane B: `4465559f` introduced the changed
initialization representation and `0e2790f3` routed canonical MLDR to the
version-stamped pick/copy/start port in `research/protocols/ic3syn/mldr.ts`.
The latter removed canonical `C0` and `Copied` setup state and used `CV` to
mark copied rows. Existing small-state counts do not establish equivalence.

We choose the coordinator's **revert** option, not an unproven equivalence
claim. Commit `94be6cdb` restores `research/protocols/ic3syn/models.ts`
byte-for-byte to `8214a543`, including its original MLDR setup/copy encoding.
The alternate standalone port remains research-only and is not imported by
the canonical 29-model roster. No 29/29 success is claimed.

## Remaining qualification

Run exact-source type/lint with child-PID RSS, cgroup and kernel OOM evidence;
all added tests, all seven full shards, Lane D's unchanged helper probe, and
three alternating baseline/candidate TIP `relaxedprefix_correct` pairs.
Preserve the previous p1 evidence job's four-error type-check failure; the
four known-present indexed accesses are corrected in `c0642345`.
Requalify the combined candidate's frozen p1 cost and whole-Paxos work.
Only after these checks request Lane D's official gate against `8214a543`.
