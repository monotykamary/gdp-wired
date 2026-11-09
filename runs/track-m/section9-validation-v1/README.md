# T-9A initial validation

Same exclusive bx_3kjzmmhv, eight pinned vCPUs. TypeScript and type-aware lint
pass. Nine tests / 15 assertions pass. A fresh process validates all 42 source
SAT models and 14 numeric SAT models against their complete original paths
(56 scope checks), across all 12 records. All original goal/certificate/path
hashes match. No pre-existing opaque-column registry is used.

See ../section9-validation-v2/ for the final stronger full-certificate, numeric
goal, active-cut and original-index mapping checks.
