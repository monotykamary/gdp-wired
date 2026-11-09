# Inv*: no quorum of a config can still be gathered for a config term held — frozen terminal source queries

These are independent diagnostic probes; their units are not charged to the original draw. See README.md for whether this is the terminal model or the preceding observed model. A refuted query must also pass the unchanged kernel check.

| Index | Instance terms | Unit | Outcome | Units | Core |
|---:|---|---:|---|---:|---:|
| 45 | 1*r$0 | 0 | refuted-checked | 16.578766 | 3 |
| 47 | 1*r$1 | 0 | sat-validated | 15.009148 | — |
| 54 | 1*r$0 | 0 | refuted-checked | 16.578766 | 3 |
| 49 | 1*r$1 + -1*r$3 | 0 | refuted-checked | 12.023989 | 3 |
| 2 | 1*r$0 + -1*r$13 | 0 | refuted-checked | 17.821772 | 4 |
| 3 | 1*r$0 + -1*r$17 | 0 | refuted-checked | 17.533430 | 3 |
| 4 | 1*r$0 + -1*r$19 | 0 | refuted-checked | 18.063464 | 5 |
| 5 | 1*r$1 + -1*r$8 | 0 | sat-validated | 16.092352 | — |
| 27 | 1*r$0 + -1*r$11 | 0 | refuted-checked | 18.902150 | 4 |
| 29 | 1*r$1 + -1*r$12 | 0 | sat-validated | 16.063516 | — |
| 32 | 1*r$1 + -1*r$9 | 0 | sat-validated | 16.095796 | — |
| 34 | 1*r$0 + -1*r$14 | 0 | refuted-checked | 18.753314 | 5 |
| 36 | 1*r$1 + -1*r$10 | 0 | sat-validated | 16.095796 | — |
| 38 | 1*r$0 + -1*r$15 | 0 | refuted-checked | 18.419231 | 4 |
| 40 | 1*r$0 + -1*r$16 | 0 | refuted-checked | 18.486836 | 3 |
| 42 | 1*r$0 + -1*r$18 | 0 | refuted-checked | 18.063313 | 3 |
| 82 | 1*r$0 + 1*r$3 + -1*r$8 | 0 | sat-validated | 23.046242 | — |
| 83 | 1*r$0 + 1*r$4 + -1*r$8 | 0 | sat-validated | 20.321710 | — |
| 86 | 1*r$1 + 1*r$3 + -1*r$8 | 0 | sat-validated | 16.934268 | — |
| 87 | 1*r$1 + 1*r$4 + -1*r$8 | 0 | sat-validated | 17.102764 | — |
| 1 | 1*r$0 + -1*r$8 | 0 | refuted-checked | 17.542045 | 3 |
| 6 | 1*r$1 + -1*r$13 | 0 | sat-validated | 16.410292 | — |
| 7 | 1*r$1 + -1*r$17 | 0 | sat-validated | 16.410292 | — |
| 8 | 1*r$1 + -1*r$19 | 0 | sat-validated | 16.410292 | — |
| 51 | 1*r$1 + -1*r$4 | 0 | sat-validated | 15.924784 | — |
| 71 | 1*r$0 + 1*r$3 + -1*r$5 + -1*r$7 + -1*r$6 | 0 | refuted-checked | 24.698926 | 4 |
| 74 | 1*r$1 + 1*r$3 + -1*r$5 + -1*r$7 + -1*r$6 | 0 | sat-validated | 17.805822 | — |
| 81 | 1*r$0 + 1*r$2 + -1*r$7 + -1*r$5 + -1*r$6 | 0 | refuted-checked | 22.693258 | 4 |
| 84 | 1*r$0 + 1*r$4 + -1*r$7 + -1*r$5 + -1*r$6 | 0 | sat-validated | 20.984392 | — |
| 85 | 1*r$1 + 1*r$2 + -1*r$7 + -1*r$5 + -1*r$6 | 0 | sat-validated | 18.689396 | — |
| 88 | 1*r$1 + 1*r$4 + -1*r$7 + -1*r$5 + -1*r$6 | 0 | sat-validated | 17.847598 | — |

The exact path, numeric goal, complete model and source hypotheses are retained in star-full.json (recoverable from the checked archive).

## Read mapping

- `r$0` = `bq#[{"op":"add","a":{"op":"mul","k":64,"a":{"op":"var","name":"a$#"}},"b":{"op":"var","name":"j$"}}]`
- `r$1` = `cfgSize#[{"op":"var","name":"a$#"}]`
- `r$2` = `inX[{"op":"const","value":0}]`
- `r$3` = `inS[{"op":"const","value":0}]`
- `r$4` = `inQ2[{"op":"const","value":0}]`
- `r$5` = `xNotS[{"op":"const","value":0}]`
- `r$6` = `xAndS[{"op":"const","value":0}]`
- `r$7` = `sNotX[{"op":"const","value":0}]`
- `r$8` = `cfgSize[{"op":"var","name":"a$#"}]`
- `r$9` = `cfgSize[{"op":"var","name":"j$"}]`
- `r$10` = `cfgSize[{"op":"const","value":0}]`
- `r$11` = `bq[{"op":"add","a":{"op":"mul","k":64,"a":{"op":"var","name":"i"}},"b":{"op":"var","name":"i"}}]`
- `r$12` = `cfgSize[{"op":"var","name":"i"}]`
- `r$13` = `bq[{"op":"add","a":{"op":"mul","k":64,"a":{"op":"var","name":"a$#"}},"b":{"op":"var","name":"i"}}]`
- `r$14` = `bq[{"op":"add","a":{"op":"mul","k":64,"a":{"op":"var","name":"i"}},"b":{"op":"var","name":"a$#"}}]`
- `r$15` = `bq[{"op":"add","a":{"op":"mul","k":64,"a":{"op":"var","name":"j$"}},"b":{"op":"var","name":"i"}}]`
- `r$16` = `bq[{"op":"add","a":{"op":"mul","k":64,"a":{"op":"var","name":"i"}},"b":{"op":"var","name":"j$"}}]`
- `r$17` = `bq[{"op":"add","a":{"op":"mul","k":64,"a":{"op":"var","name":"a$#"}},"b":{"op":"var","name":"j$"}}]`
- `r$18` = `bq[{"op":"add","a":{"op":"mul","k":64,"a":{"op":"const","value":0}},"b":{"op":"var","name":"j$"}}]`
- `r$19` = `bq[{"op":"add","a":{"op":"mul","k":64,"a":{"op":"var","name":"a$#"}},"b":{"op":"const","value":0}}]`
