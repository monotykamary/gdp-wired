# Initial validation (not the final pass)

Static checks passed. 227 targeted tests passed; three new test fixtures failed
because they attempted root collection of scope-local trees or assumed unused
invalid products were kernel refusals. The production implementation was not
changed for those failures: fixtures now transport to the empty root, and the
product test follows the unchanged kernel behavior. Exact raw output is retained
in `validate.log.gz`; the plain-text view trims one trailing diagnostic space.
