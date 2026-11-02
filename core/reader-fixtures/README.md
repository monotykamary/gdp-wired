# Reader-fuzz regressions

These are the exact mutated sources captured by `READER_FUZZ_SHOW=1`, with
`READER_FUZZ_N=2`, on base 9b62ecf. Each filename names the language and seed.
The TypeScript source has a `.txt` suffix so the repository typecheck does not
try to compile intentionally invalid syntax. Tests copy JVM/Go sources into
isolated temporary projects so sibling fixtures cannot affect resolution.

- Swift 735726, 739158, 744834: native reader recovery exceeded 300 seconds.
- Swift 735990, 746946: the native reader returned, but `swift build` timed out
  twice. Reproduced with a diagnostic 30-second build limit; the archived
  treadmill used the default 900 seconds per attempt.
- JVM 737430: Kotlin PSI recovery exceeded 300 seconds.
- JVM 724362: a missing `if` branch reached `where(null)`.
- JVM 765282: a nameless function reached `Set.of(...).contains(null)`.
- TypeScript 673062: an empty extends clause reached `h.types[0].expression`.
- Go 685506: a return value in a zero-result function reached `results[0].t`.
- C++ 693042: a narrowing initializer introduced division, which kernel start
  expressions do not permit (they read only parameters, not functions).

Native reader depth guards are deliberately conservative text resource limits:
32 nested delimiter characters, **including strings and comments**. Refusing
that resource limit does not assert that a source is syntactically invalid.
Swift also limits each build-check attempt to 60 seconds (or the smaller
`GDP_COMPILE_S` setting). Compiler failure remains a failed check, not evidence
that the source differs from the extracted rule. No kernel admission changed.

Original replay logs: `runs/repro-2/` and `runs/compiler-repro/`.
