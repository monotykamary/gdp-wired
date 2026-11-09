# Inv*: no quorum of a config can still be gathered for a config term held — frozen terminal source queries

These are independent diagnostic probes; their units are not charged to the original draw. See README.md for whether this is the terminal model or the preceding observed model. A refuted query must also pass the unchanged kernel check.

| Index | Instance terms | Unit | Outcome | Units | Core |
|---:|---|---:|---|---:|---:|
| 45 | 1*r$0 | 0 | sat-validated | 24.967622 | — |
| 47 | 1*r$1 | 0 | sat-validated | 14.883128 | — |
| 54 | 1*r$0 | 0 | sat-validated | 24.967622 | — |
| 49 | 1*r$1 + -1*r$3 | 0 | sat-validated | 13.094888 | — |
| 2 | 1*r$0 + -1*r$13 | 0 | sat-validated | 25.200028 | — |
| 3 | 1*r$0 + -1*r$17 | 0 | refuted-checked | 25.020353 | 2 |
| 4 | 1*r$0 + -1*r$19 | 0 | sat-validated | 25.728482 | — |
| 5 | 1*r$1 + -1*r$8 | 0 | refuted-checked | 13.416827 | 2 |
| 27 | 1*r$0 + -1*r$11 | 0 | sat-validated | 27.729922 | — |
| 29 | 1*r$1 + -1*r$12 | 0 | sat-validated | 17.768570 | — |
| 32 | 1*r$1 + -1*r$9 | 0 | refuted-checked | 20.439056 | 2 |
| 34 | 1*r$0 + -1*r$14 | 0 | sat-validated | 27.731890 | — |
| 36 | 1*r$1 + -1*r$10 | 0 | sat-validated | 16.056480 | — |
| 38 | 1*r$0 + -1*r$15 | 0 | sat-validated | 48.876348 | — |
| 40 | 1*r$0 + -1*r$16 | 0 | sat-validated | 27.731890 | — |
| 42 | 1*r$0 + -1*r$18 | 0 | sat-validated | 27.419168 | — |
| 82 | 1*r$0 + 1*r$3 + -1*r$8 | 0 | sat-validated | 24.648672 | — |
| 83 | 1*r$0 + 1*r$4 + -1*r$8 | 0 | sat-validated | 26.949214 | — |
| 86 | 1*r$1 + 1*r$3 + -1*r$8 | 0 | sat-validated | 15.994416 | — |
| 87 | 1*r$1 + 1*r$4 + -1*r$8 | 0 | sat-validated | 16.938656 | — |
| 1 | 1*r$0 + -1*r$8 | 0 | refuted-checked | 17.150839 | 2 |
| 6 | 1*r$1 + -1*r$13 | 0 | sat-validated | 19.769568 | — |
| 7 | 1*r$1 + -1*r$17 | 0 | sat-validated | 23.129766 | — |
| 8 | 1*r$1 + -1*r$19 | 0 | sat-validated | 19.792424 | — |
| 51 | 1*r$1 + -1*r$4 | 0 | sat-validated | 13.002176 | — |
| 71 | 1*r$0 + 1*r$3 + -1*r$5 + -1*r$7 + -1*r$6 | 0 | sat-validated | 22.922652 | — |
| 74 | 1*r$1 + 1*r$3 + -1*r$5 + -1*r$7 + -1*r$6 | 0 | sat-validated | 16.603388 | — |
| 81 | 1*r$0 + 1*r$2 + -1*r$7 + -1*r$5 + -1*r$6 | 0 | sat-validated | 22.835306 | — |
| 84 | 1*r$0 + 1*r$4 + -1*r$7 + -1*r$5 + -1*r$6 | 0 | sat-validated | 23.266590 | — |
| 85 | 1*r$1 + 1*r$2 + -1*r$7 + -1*r$5 + -1*r$6 | 0 | sat-validated | 15.889480 | — |
| 88 | 1*r$1 + 1*r$4 + -1*r$7 + -1*r$5 + -1*r$6 | 0 | sat-validated | 17.026412 | — |

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
