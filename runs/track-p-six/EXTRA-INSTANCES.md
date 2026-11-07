# Six STEP emitter audit: every extra PRE tuple

Historical emitter-only, all-input-flag/polarity-selector audit of ad4fe53e10f783a7e7b095eb3170203a5e5d83e1b239e4c39c47f2bae7850e5f. This is not the full production selector/reservation path. Full phase and semantic-witness mappings remain in the linked per-target JSON files documented by `runs/REPORT.md`. A failed or SAT partial request is not a reachable protocol counterexample.

Names `C<i>` refer to indices in the unchanged original family fixture. Witness spelling is local to each audit; it does not add an equality.

## C7: 64 extra tuples

| Source law/flag | Exact tuple in final observed audit phase |
|---|---|
| `?noProposal` | `key$2#` |
| `?noProposal` | `key$3` |
| `?noProposal` | `key$4` |
| `?noProposal` | `key$5` |
| `?noProposal` | `op` |
| `?noProposal` | `n` |
| `?noProposal` | `r` |
| `?noProposal` | `v` |
| `?noProposal` | `maxr` |
| `?noProposal` | `w` |
| `?joined` | `key$2#` |
| `?joined` | `key$3` |
| `?joined` | `key$4` |
| `?joined` | `key$5` |
| `?joined` | `op` |
| `?joined` | `n` |
| `?joined` | `r` |
| `?joined` | `v` |
| `?joined` | `maxr` |
| `?joined` | `w` |
| `?rowOk` | `key$2#` |
| `?rowOk` | `key$3` |
| `?rowOk` | `key$4` |
| `?rowOk` | `key$5` |
| `?rowOk` | `op` |
| `?rowOk` | `n` |
| `?rowOk` | `r` |
| `?rowOk` | `v` |
| `?rowOk` | `maxr` |
| `?rowOk` | `w` |
| `?all$1` | `key$2#` |
| `?all$1` | `key$3` |
| `?all$1` | `key$4` |
| `?all$1` | `key$5` |
| `?all$1` | `op` |
| `?all$1` | `n` |
| `?all$1` | `r` |
| `?all$1` | `v` |
| `?all$1` | `maxr` |
| `?all$1` | `w` |
| C9 | `0` |
| C17 | `r, v` |
| C17 | `key$2#, v` |
| C10 | `r, v` |
| C33 | `key$2#, key$3, pv` |
| C33 | `key$4, key$5, pv` |
| C4 | `((4096*(w$0)+64*(r))+v)` |
| C4 | `((4096*(w$1)+64*(r))+v)` |
| C4 | `((4096*(w$2)+64*(r))+v)` |
| C4 | `((4096*(w$2)+64*(key$2#))+key$3)` |
| C14 | `w$0, (64*(r)+v)` |
| C14 | `w$1, (64*(r)+v)` |
| C14 | `w$2, (64*(r)+v)` |
| C14 | `w$2, (64*(key$2#)+key$3)` |
| C45 | `w$0, r, v` |
| C45 | `w$1, r, v` |
| C45 | `w$2, r, v` |
| C45 | `w$2, key$2#, key$3` |
| C74 | `w$1` |
| C74 | `w$8` |
| C2 | `(64*(w$5)+r)` |
| C2 | `(64*(w$6)+key$2#)` |
| C2 | `(64*(w$7)+key$4)` |
| C61 | `v` |

## C10: 62 extra tuples

| Source law/flag | Exact tuple in final observed audit phase |
|---|---|
| `?noProposal` | `a$c#` |
| `?noProposal` | `b$c` |
| `?noProposal` | `op` |
| `?noProposal` | `n` |
| `?noProposal` | `r` |
| `?noProposal` | `v` |
| `?noProposal` | `maxr` |
| `?noProposal` | `w` |
| `?joined` | `a$c#` |
| `?joined` | `b$c` |
| `?joined` | `op` |
| `?joined` | `n` |
| `?joined` | `r` |
| `?joined` | `v` |
| `?joined` | `maxr` |
| `?joined` | `w` |
| `?rowOk` | `a$c#` |
| `?rowOk` | `b$c` |
| `?rowOk` | `op` |
| `?rowOk` | `n` |
| `?rowOk` | `r` |
| `?rowOk` | `v` |
| `?rowOk` | `maxr` |
| `?rowOk` | `w` |
| `?all$1` | `a$c#` |
| `?all$1` | `b$c` |
| `?all$1` | `op` |
| `?all$1` | `n` |
| `?all$1` | `r` |
| `?all$1` | `v` |
| `?all$1` | `maxr` |
| `?all$1` | `w` |
| C9 | `0` |
| C17 | `a$c#, b$c` |
| C17 | `r, v` |
| C17 | `r, a$c#` |
| C17 | `r, b$c` |
| C11 | `r, v, a$c#, b$c` |
| C11 | `a$c#, b$c, r, v` |
| C11 | `a$c#, b$c, r, a$c#` |
| C11 | `a$c#, b$c, r, b$c` |
| C33 | `a$c#, b$c, v` |
| C33 | `a$c#, b$c, pv` |
| C4 | `((4096*(wOld)+64*(a$c#))+b$c)` |
| C4 | `((4096*(w$73)+64*(r))+v)` |
| C4 | `((4096*(w$73)+64*(a$c#))+b$c)` |
| C14 | `wOld, (64*(a$c#)+b$c)` |
| C14 | `w$73, (64*(r)+v)` |
| C14 | `w$73, (64*(a$c#)+b$c)` |
| C14 | `cnt, r` |
| C45 | `wOld, a$c#, b$c` |
| C45 | `w$73, r, v` |
| C45 | `w$73, a$c#, b$c` |
| C45 | `n, r, v` |
| C7 | `a$c#, b$c, r, v` |
| C7 | `r, v, a$c#, b$c` |
| C7 | `a$c#, b$c, a$c#, b$c` |
| C7 | `r, v, r, v` |
| C61 | `v` |
| C70 | `a$c#, r, b$c` |
| C70 | `r, r, v` |
| C74 | `v` |

## C11: 51 extra tuples

| Source law/flag | Exact tuple in final observed audit phase |
|---|---|
| `?noProposal` | `a$c#` |
| `?noProposal` | `b$c` |
| `?noProposal` | `c$c` |
| `?noProposal` | `d$c` |
| `?noProposal` | `op` |
| `?noProposal` | `n` |
| `?noProposal` | `r` |
| `?noProposal` | `v` |
| `?noProposal` | `maxr` |
| `?noProposal` | `w` |
| `?joined` | `a$c#` |
| `?joined` | `b$c` |
| `?joined` | `c$c` |
| `?joined` | `d$c` |
| `?joined` | `op` |
| `?joined` | `n` |
| `?joined` | `r` |
| `?joined` | `v` |
| `?joined` | `maxr` |
| `?joined` | `w` |
| `?rowOk` | `a$c#` |
| `?rowOk` | `b$c` |
| `?rowOk` | `c$c` |
| `?rowOk` | `d$c` |
| `?rowOk` | `op` |
| `?rowOk` | `n` |
| `?rowOk` | `r` |
| `?rowOk` | `v` |
| `?rowOk` | `maxr` |
| `?rowOk` | `w` |
| `?all$1` | `a$c#` |
| `?all$1` | `b$c` |
| `?all$1` | `c$c` |
| `?all$1` | `d$c` |
| `?all$1` | `op` |
| `?all$1` | `n` |
| `?all$1` | `r` |
| `?all$1` | `v` |
| `?all$1` | `maxr` |
| `?all$1` | `w` |
| C3 | `(64*(c$c)+d$c)` |
| C17 | `c$c, d$c` |
| C33 | `c$c, d$c, pv` |
| C33 | `c$c, d$c, v` |
| C10 | `c$c, d$c` |
| C10 | `a$c#, b$c` |
| C10 | `pr, pv` |
| C2 | `(64*(wDiff)+a$c#)` |
| C4 | `((4096*(wDiff)+64*(a$c#))+b$c)` |
| C14 | `wDiff, (64*(a$c#)+b$c)` |
| C45 | `wDiff, a$c#, b$c` |

## C17: 69 extra tuples

| Source law/flag | Exact tuple in final observed audit phase |
|---|---|
| `?noProposal` | `key1$enum#` |
| `?noProposal` | `key2$enum` |
| `?noProposal` | `op` |
| `?noProposal` | `n` |
| `?noProposal` | `r` |
| `?noProposal` | `v` |
| `?noProposal` | `maxr` |
| `?noProposal` | `w` |
| `?joined` | `key1$enum#` |
| `?joined` | `key2$enum` |
| `?joined` | `op` |
| `?joined` | `n` |
| `?joined` | `r` |
| `?joined` | `v` |
| `?joined` | `maxr` |
| `?joined` | `w` |
| `?rowOk` | `key1$enum#` |
| `?rowOk` | `key2$enum` |
| `?rowOk` | `op` |
| `?rowOk` | `n` |
| `?rowOk` | `r` |
| `?rowOk` | `v` |
| `?rowOk` | `maxr` |
| `?rowOk` | `w` |
| `?all$1` | `key1$enum#` |
| `?all$1` | `key2$enum` |
| `?all$1` | `op` |
| `?all$1` | `n` |
| `?all$1` | `r` |
| `?all$1` | `v` |
| `?all$1` | `maxr` |
| `?all$1` | `w` |
| C9 | `0` |
| C33 | `key1$enum#, key2$enum, pv` |
| C33 | `key1$enum#, key2$enum, v` |
| C10 | `key1$enum#, key2$enum` |
| C10 | `pr, pv` |
| C10 | `r, v` |
| C11 | `pr, pv, key1$enum#, key2$enum` |
| C11 | `r, v, key1$enum#, key2$enum` |
| C11 | `key1$enum#, key2$enum, pr, pv` |
| C11 | `key1$enum#, key2$enum, r, v` |
| C4 | `((4096*(w$0)+64*(r))+v)` |
| C4 | `((4096*(w$1)+64*(r))+v)` |
| C4 | `((4096*(w$2)+64*(r))+v)` |
| C4 | `((4096*(w$2)+64*(key1$enum#))+key2$enum)` |
| C14 | `w$0, (64*(r)+v)` |
| C14 | `w$1, (64*(r)+v)` |
| C14 | `w$2, (64*(r)+v)` |
| C14 | `w$2, (64*(key1$enum#)+key2$enum)` |
| C45 | `w$0, r, v` |
| C45 | `w$1, r, v` |
| C45 | `w$2, r, v` |
| C45 | `w$2, key1$enum#, key2$enum` |
| C74 | `w$1` |
| C74 | `w$8` |
| C74 | `v` |
| C2 | `(64*(w$5)+pr)` |
| C2 | `(64*(w$6)+r)` |
| C2 | `(64*(w$7)+key1$enum#)` |
| C7 | `key1$enum#, key2$enum, pr, pv` |
| C7 | `key1$enum#, key2$enum, r, v` |
| C7 | `pr, pv, key1$enum#, key2$enum` |
| C7 | `r, v, key1$enum#, key2$enum` |
| C61 | `key2$enum` |
| C61 | `pv` |
| C61 | `v` |
| C70 | `key1$enum#, r, key2$enum` |
| C70 | `r, r, v` |

## C33: 77 extra tuples

| Source law/flag | Exact tuple in final observed audit phase |
|---|---|
| `?noProposal` | `key1$enum#` |
| `?noProposal` | `key2$enum` |
| `?noProposal` | `key3$enum` |
| `?noProposal` | `op` |
| `?noProposal` | `n` |
| `?noProposal` | `r` |
| `?noProposal` | `v` |
| `?noProposal` | `maxr` |
| `?noProposal` | `w` |
| `?joined` | `key1$enum#` |
| `?joined` | `key2$enum` |
| `?joined` | `key3$enum` |
| `?joined` | `op` |
| `?joined` | `n` |
| `?joined` | `r` |
| `?joined` | `v` |
| `?joined` | `maxr` |
| `?joined` | `w` |
| `?rowOk` | `key1$enum#` |
| `?rowOk` | `key2$enum` |
| `?rowOk` | `key3$enum` |
| `?rowOk` | `op` |
| `?rowOk` | `n` |
| `?rowOk` | `r` |
| `?rowOk` | `v` |
| `?rowOk` | `maxr` |
| `?rowOk` | `w` |
| `?all$1` | `key1$enum#` |
| `?all$1` | `key2$enum` |
| `?all$1` | `key3$enum` |
| `?all$1` | `op` |
| `?all$1` | `n` |
| `?all$1` | `r` |
| `?all$1` | `v` |
| `?all$1` | `maxr` |
| `?all$1` | `w` |
| C9 | `0` |
| C17 | `key1$enum#, key2$enum` |
| C17 | `key1$enum#, key3$enum` |
| C17 | `pr, pv` |
| C17 | `key1$enum#, pv` |
| C33 | `key1$enum#, key2$enum, pv` |
| C33 | `key1$enum#, key3$enum, pv` |
| C33 | `key1$enum#, key2$enum, v` |
| C10 | `key1$enum#, key2$enum` |
| C10 | `key1$enum#, key3$enum` |
| C10 | `pr, pv` |
| C11 | `pr, pv, key1$enum#, key2$enum` |
| C11 | `pr, pv, key1$enum#, key3$enum` |
| C11 | `key1$enum#, key2$enum, pr, pv` |
| C11 | `key1$enum#, key3$enum, pr, pv` |
| C74 | `w$0` |
| C74 | `w$7` |
| C74 | `w$8` |
| C74 | `w$9` |
| C4 | `((4096*(w$1)+64*(key1$enum#))+key2$enum)` |
| C4 | `((4096*(w$2)+64*(key1$enum#))+key3$enum)` |
| C4 | `((4096*(w$3)+64*(pr))+pv)` |
| C4 | `((4096*(w$4)+64*(pr))+pv)` |
| C14 | `w$1, (64*(key1$enum#)+key2$enum)` |
| C14 | `w$2, (64*(key1$enum#)+key3$enum)` |
| C14 | `w$3, (64*(pr)+pv)` |
| C14 | `w$4, (64*(pr)+pv)` |
| C45 | `w$1, key1$enum#, key2$enum` |
| C45 | `w$2, key1$enum#, key3$enum` |
| C45 | `w$3, pr, pv` |
| C45 | `w$4, pr, pv` |
| C2 | `(64*(w$4)+pr)` |
| C2 | `(64*(w$5)+key1$enum#)` |
| C2 | `(64*(w$6)+key1$enum#)` |
| C7 | `key1$enum#, key2$enum, pr, pv` |
| C7 | `key1$enum#, key3$enum, pr, pv` |
| C7 | `pr, pv, key1$enum#, key2$enum` |
| C7 | `pr, pv, key1$enum#, key3$enum` |
| C61 | `pv` |
| C70 | `key1$enum#, r, key2$enum` |
| C70 | `key1$enum#, r, key3$enum` |

## C66: 60 extra tuples

| Source law/flag | Exact tuple in final observed audit phase |
|---|---|
| `?noProposal` | `op` |
| `?noProposal` | `n` |
| `?noProposal` | `r` |
| `?noProposal` | `v` |
| `?noProposal` | `maxr` |
| `?noProposal` | `w` |
| `?joined` | `op` |
| `?joined` | `n` |
| `?joined` | `r` |
| `?joined` | `v` |
| `?joined` | `maxr` |
| `?joined` | `w` |
| `?rowOk` | `op` |
| `?rowOk` | `n` |
| `?rowOk` | `r` |
| `?rowOk` | `v` |
| `?rowOk` | `maxr` |
| `?rowOk` | `w` |
| `?all$1` | `op` |
| `?all$1` | `n` |
| `?all$1` | `r` |
| `?all$1` | `v` |
| `?all$1` | `maxr` |
| `?all$1` | `w` |
| C9 | `0` |
| C10 | `pmaxr, pv` |
| C10 | `pr, pv` |
| C11 | `pr, pv, pmaxr, pv` |
| C11 | `pmaxr, pv, pr, pv` |
| C11 | `pmaxr, pv, pmaxr, pv` |
| C11 | `pmaxr, pv, r, op` |
| C33 | `pmaxr, pv, v` |
| C74 | `w$0` |
| C74 | `w$5` |
| C74 | `w$6` |
| C74 | `w$7` |
| C4 | `((4096*(w$1)+64*(pmaxr))+pv)` |
| C4 | `((4096*(w$2)+64*(pr))+pv)` |
| C4 | `((4096*(w$3)+64*(pr))+pv)` |
| C4 | `((4096*(w$4)+64*(pmaxr))+pv)` |
| C14 | `w$1, (64*(pmaxr)+pv)` |
| C14 | `w$2, (64*(pr)+pv)` |
| C14 | `w$3, (64*(pr)+pv)` |
| C14 | `w$4, (64*(pmaxr)+pv)` |
| C45 | `w$1, pmaxr, pv` |
| C45 | `w$2, pr, pv` |
| C45 | `w$3, pr, pv` |
| C45 | `w$4, pmaxr, pv` |
| C2 | `(64*(w$3)+pr)` |
| C2 | `(64*(w$4)+pmaxr)` |
| C2 | `(64*(w$7)+pr)` |
| C2 | `(64*(w$8)+pmaxr)` |
| C7 | `pmaxr, pv, pr, pv` |
| C7 | `pr, pv, pmaxr, pv` |
| C7 | `pmaxr, pv, pmaxr, pv` |
| C7 | `pr, pv, pr, pv` |
| C17 | `pmaxr, pv` |
| C17 | `pr, pv` |
| C17 | `{"op":"if","c":{"op":"and","xs":[{"op":"=","a":{"op":"var","name":"op"},"b":{"op":"const","value":2}},{"op":"and","xs":[{"op":"=","a":{"op":"var","name":"busy"},"b":{"op":"const","value":0}},{"op":"not","x":{"op":"=","a":{"op":"var","name":"r"},"b":{"op":"var","name":"none"}}}]},{"op":"=","a":{"op":"var","name":"?noProposal"},"b":{"op":"const","value":1}},{"op":"=","a":{"op":"var","name":"?joined"},"b":{"op":"const","value":1}},{"op":"or","xs":[{"op":"=","a":{"op":"var","name":"maxr"},"b":{"op":"var","name":"none"}},{"op":"and","xs":[{"op":"<=","a":{"op":"const","value":1},"b":{"op":"get","map":"Q","key":{"op":"var","name":"w"}}},{"op":"<","a":{"op":"var","name":"maxr"},"b":{"op":"var","name":"r"}},{"op":"=","a":{"op":"get","map":"Vote","key":{"op":"add","a":{"op":"add","a":{"op":"mul","k":4096,"a":{"op":"var","name":"w"}},"b":{"op":"mul","k":64,"a":{"op":"var","name":"maxr"}}},"b":{"op":"var","name":"v"}}},"b":{"op":"const","value":1}}]}]}]},"then":{"op":"var","name":"maxr"},"else":{"op":"if","c":{"op":"or","xs":[{"op":"and","xs":[{"op":"and","xs":[{"op":"=","a":{"op":"var","name":"op"},"b":{"op":"const","value":3}},{"op":"=","a":{"op":"var","name":"busy"},"b":{"op":"const","value":1}}]},{"op":"=","a":{"op":"get","map":"Qs","key":{"op":"var","name":"cnt"}},"b":{"op":"const","value":1}},{"op":"not","x":{"op":"=","a":{"op":"var","name":"?rowOk"},"b":{"op":"const","value":1}}}]},{"op":"and","xs":[{"op":"and","xs":[{"op":"=","a":{"op":"var","name":"op"},"b":{"op":"const","value":3}},{"op":"=","a":{"op":"var","name":"busy"},"b":{"op":"const","value":1}}]},{"op":"not","x":{"op":"and","xs":[{"op":"and","xs":[{"op":"=","a":{"op":"var","name":"op"},"b":{"op":"const","value":3}},{"op":"=","a":{"op":"var","name":"busy"},"b":{"op":"const","value":1}}]},{"op":"=","a":{"op":"get","map":"Qs","key":{"op":"var","name":"cnt"}},"b":{"op":"const","value":1}},{"op":"not","x":{"op":"=","a":{"op":"var","name":"?rowOk"},"b":{"op":"const","value":1}}}]}},{"op":"=","a":{"op":"add","a":{"op":"var","name":"cnt"},"b":{"op":"const","value":1}},"b":{"op":"var","name":"size"}}]}]},"then":{"op":"const","value":0},"else":{"op":"var","name":"pmaxr"}}}, {"op":"if","c":{"op":"and","xs":[{"op":"=","a":{"op":"var","name":"op"},"b":{"op":"const","value":2}},{"op":"and","xs":[{"op":"=","a":{"op":"var","name":"busy"},"b":{"op":"const","value":0}},{"op":"not","x":{"op":"=","a":{"op":"var","name":"r"},"b":{"op":"var","name":"none"}}}]},{"op":"=","a":{"op":"var","name":"?noProposal"},"b":{"op":"const","value":1}},{"op":"=","a":{"op":"var","name":"?joined"},"b":{"op":"const","value":1}},{"op":"or","xs":[{"op":"=","a":{"op":"var","name":"maxr"},"b":{"op":"var","name":"none"}},{"op":"and","xs":[{"op":"<=","a":{"op":"const","value":1},"b":{"op":"get","map":"Q","key":{"op":"var","name":"w"}}},{"op":"<","a":{"op":"var","name":"maxr"},"b":{"op":"var","name":"r"}},{"op":"=","a":{"op":"get","map":"Vote","key":{"op":"add","a":{"op":"add","a":{"op":"mul","k":4096,"a":{"op":"var","name":"w"}},"b":{"op":"mul","k":64,"a":{"op":"var","name":"maxr"}}},"b":{"op":"var","name":"v"}}},"b":{"op":"const","value":1}}]}]}]},"then":{"op":"var","name":"v"},"else":{"op":"if","c":{"op":"or","xs":[{"op":"and","xs":[{"op":"and","xs":[{"op":"=","a":{"op":"var","name":"op"},"b":{"op":"const","value":3}},{"op":"=","a":{"op":"var","name":"busy"},"b":{"op":"const","value":1}}]},{"op":"=","a":{"op":"get","map":"Qs","key":{"op":"var","name":"cnt"}},"b":{"op":"const","value":1}},{"op":"not","x":{"op":"=","a":{"op":"var","name":"?rowOk"},"b":{"op":"const","value":1}}}]},{"op":"and","xs":[{"op":"and","xs":[{"op":"=","a":{"op":"var","name":"op"},"b":{"op":"const","value":3}},{"op":"=","a":{"op":"var","name":"busy"},"b":{"op":"const","value":1}}]},{"op":"not","x":{"op":"and","xs":[{"op":"and","xs":[{"op":"=","a":{"op":"var","name":"op"},"b":{"op":"const","value":3}},{"op":"=","a":{"op":"var","name":"busy"},"b":{"op":"const","value":1}}]},{"op":"=","a":{"op":"get","map":"Qs","key":{"op":"var","name":"cnt"}},"b":{"op":"const","value":1}},{"op":"not","x":{"op":"=","a":{"op":"var","name":"?rowOk"},"b":{"op":"const","value":1}}}]}},{"op":"=","a":{"op":"add","a":{"op":"var","name":"cnt"},"b":{"op":"const","value":1}},"b":{"op":"var","name":"size"}}]}]},"then":{"op":"const","value":0},"else":{"op":"var","name":"pv"}}}` |
| C61 | `pv` |
