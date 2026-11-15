# Nested public capture

`proveRule` now publishes only the outermost synchronous public invocation.
Nested Skolem searches still retain their complete producer chain, but do not
emit extra public events. Scope depth is restored by `finally`, including when
an invocation throws. The default-off observer does not alter returned objects.

Verified with pinned Bun 1.4.3 in strict-once batch
`20261115-221304-m1rdnd` (tree `4e718f4580d9`):

- Typecheck and commitlint passed.
- 28 tests, 205 assertions, zero failures.
- The real public Skolem fixture ran once in each fresh ON/OFF process.
- Native verdicts and every native work counter matched exactly.
- ON retained a complete closure with one actual Skolem derivation and one outer
  public event. Its capsule was read back successfully.
- Source projection deliberately remains **unqualified**: a checked witness
  source bridge is still required. This capture fix makes no new all-size claim.

Artifacts: `runs/bapa-nested-capture-02/nested-capture-gate.files/`, especially
`parity.json`, `on.json`, `off.json`, and `tests.log`.
