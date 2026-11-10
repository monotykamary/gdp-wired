# Additional untrusted phase boundaries — NOT VALIDATED

boundaries.patch adds table-build, instance-construction and kernel-check
observations at call sites in kernel/prove.ts and core/counts.ts. No callback
is introduced into a trusted checker. Existing ptime phases already cover
sampling, cube inference, finite filtering, encoding and count-set checking.

The patch is relative to the current ledger private index, before constructors.
Its base tree is retained in /tmp/lane-i-ledger-boundaries-base-tree; temporary
source files and the separate index are named in REPORT. It is deliberately
not in the active ledger validation input. Type narrowing across the new
closures and trace-on/off equality still require verification before use.
