# Combined accounting verification — prepared, NOT LAUNCHED

Needs the generated constructor patch and its frozen identity before launch.
Do not substitute the pre-constructor input: the exact-node tests and AST
identity audit require the real generated wrappers.

The plain job runs the expanded checker erasure audit, new exact-count tests,
prior I2 cases, direct inference tests, roster, decoder and type/lint.
Three separate jobs perturb all six raw fields while checking the kernel and
solver/rational refusal suites. They intentionally leave fullWork in legacy
mode: this is an acceptance-noninterference test, not a budget qualification.

The helper audit checks that observeAst charges one after evaluating its
argument and returns the identical node; checker erasure removes only that
identity call, discarded additive writes and their dedicated imports.
