model name	: AMD Ryzen 9 9950X 16-Core Processor
SIDE mine
[infer runs] {"samples":3000,"trials":0}
[infer] runs {"ms":8,"counted":0,"work":0,"tries":0,"rows":0,"evals":0,"watched":0,"erows":0,"etries":0,"samples":3000,"trials":0}
[infer join small domains] {"params":"{\"size\":3}","doms":"op:0/1/2 ps:0/1/2 pd:0/1/2 sw0:0/1/2 sw1:0/1/2 nondet:0/1/2","combos":729}
[infer join small instance] {"states":6011,"bfs":478,"params":1,"symmetric":"","ms":1502,"took":1502}
{"id":"learning_switch","count":16,"wallMs":98815.203236,"phases":{"guards":5.801632000000012,"small":92663.434136,"candidates":6133.983025999987},"states":[750,3420],"counts":[],"cprof":{"small":0.034444999997504056,"cubes":5654.151054999995,"filter":459.66822100001446,"quorumFilter":0.009376999994
PROFILE
**Top 10:** `go` 12.5%, `evalC` 9.9%, `every` 9.6%, `map` 9.4%, `some` 6.2%, `evalE` 6.2%, `go` 5.5%, `evalE` 3.8%, `evalE` 3.6%, `evalC` 3.5%
| 12.5% | 12.40s | 100.0% | 331.26s | `go` | `/work/gdp-wired/core/machine.ts:513` |
| 9.9% | 9.87s | 9.9% | 9.87s | `evalC` | `/work/gdp-wired/core/machine.ts:395` |
| 9.6% | 9.58s | 55.7% | 55.20s | `every` | `[native code]` |
| 9.4% | 9.31s | 100.0% | 194.74s | `map` | `[native code]` |
| 6.2% | 6.15s | 82.6% | 81.77s | `some` | `[native code]` |
| 6.2% | 6.14s | 20.7% | 20.56s | `evalE` | `/work/gdp-wired/core/machine.ts:350` |
| 5.5% | 5.53s | 71.1% | 70.43s | `go` | `/work/gdp-wired/core/machine.ts:514` |
| 3.8% | 3.82s | 3.8% | 3.82s | `evalE` | `/work/gdp-wired/core/machine.ts:340` |
| 3.6% | 3.60s | 3.6% | 3.60s | `evalE` | `/work/gdp-wired/core/machine.ts` |
| 3.5% | 3.54s | 4.7% | 4.73s | `evalC` | `/work/gdp-wired/core/machine.ts:401` |
| 3.1% | 3.11s | 15.9% | 15.82s | `evalC` | `/work/gdp-wired/core/machine.ts:397` |
| 2.4% | 2.39s | 2.4% | 2.39s | `(anonymous)` | `/work/gdp-wired/core/machine.ts` |
| 2.1% | 2.17s | 54.5% | 53.95s | `evalC` | `/work/gdp-wired/core/machine.ts:399` |
| 1.7% | 1.70s | 11.6% | 11.52s | `evalE` | `/work/gdp-wired/core/machine.ts:355` |
| 1.4% | 1.48s | 82.7% | 81.86s | `evalC` | `/work/gdp-wired/core/machine.ts:400` |
| 1.3% | 1.32s | 54.5% | 54.00s | `evalE` | `/work/gdp-wired/core/machine.ts:349` |
| 1.1% | 1.10s | 4.4% | 4.35s | `evalC` | `/work/gdp-wired/core/machine.ts:398` |
| 1.0% | 1.00s | 1.0% | 1.00s | `entries` | `[native code]` |
| 0.9% | 974.8ms | 1.5% | 1.51s | `partsOf` | `/work/gdp-wired/core/machine.ts:323` |
| 0.6% | 675.4ms | 0.6% | 678.8ms | `breakKeys` | `/work/gdp-wired/core/machine.ts:301` |
| 0.5% | 568.6ms | 0.5% | 568.6ms | `evalE` | `/work/gdp-wired/core/machine.ts:341` |
| 0.5% | 552.5ms | 0.5% | 552.5ms | `evalC` | `/work/gdp-wired/core/machine.ts:402` |
| 0.5% | 515.5ms | 0.5% | 515.5ms | `Set` | `[native code]` |
| 0.4% | 473.6ms | 0.4% | 473.6ms | `cunpair` | `/work/gdp-wired/core/machine.ts:172` |
| 0.4% | 469.7ms | 0.4% | 469.7ms | `stringify` | `[native code]` |
| 0.4% | 450.7ms | 0.4% | 455.0ms | `sort` | `[native code]` |
| 0.4% | 413.2ms | 0.4% | 413.2ms | `RangeError` | `[native code]` |
| 0.3% | 316.4ms | 2.5% | 2.55s | `forEach` | `[native code]` |
SIDE base
[infer runs] {"samples":3000,"trials":0}
[infer] runs {"ms":177,"counted":0,"work":0,"tries":0,"rows":0,"evals":0,"watched":0,"erows":0,"etries":0,"samples":3000,"trials":0}
[infer join small domains] {"params":"{\"size\":3}","doms":"op:0/1/2 ps:0/1/2 pd:0/1/2 sw0:0/1/2 sw1:0/1/2 nondet:0/1/2","combos":729}
[infer join small instance] {"states":6011,"bfs":478,"params":1,"symmetric":"","ms":1502,"took":1502}
{"id":"learning_switch","count":16,"wallMs":405758.264393,"phases":{"guards":3.797424999999997,"small":392069.13014100003,"candidates":13619.857094999985},"states":[750,3420],"counts":[],"cprof":{"small":0.0927739999606274,"cubes":12912.78822300001,"filter":633.8501969999634,"quorumFilter":0.0136550
PROFILE
**Top 10:** `go` 9.2%, `evalC` 7.2%, `fromEntries` 6.8%, `copyDataProperties` 6.5%, `map` 5.8%, `(anonymous)` 5.4%, `cloneObject` 5.1%, `evalC` 4.5%, `stringify` 3.9%, `(anonymous)` 3.6%
| 9.2% | 37.62s | 100.0% | 1292.71s | `go` | `/work/gdp-wired/base/core/machine.ts:498` |
| 7.2% | 29.34s | 7.2% | 29.34s | `evalC` | `/work/gdp-wired/base/core/machine.ts:395` |
| 6.8% | 27.85s | 7.1% | 28.86s | `fromEntries` | `[native code]` |
| 6.5% | 26.53s | 6.5% | 26.53s | `copyDataProperties` | `[native code]` |
| 5.8% | 23.84s | 100.0% | 898.12s | `map` | `[native code]` |
| 5.4% | 22.05s | 5.4% | 22.05s | `(anonymous)` | `/work/gdp-wired/base/core/machine.ts:488` |
| 5.1% | 20.88s | 5.1% | 20.88s | `cloneObject` | `[native code]` |
| 4.5% | 18.29s | 4.5% | 18.29s | `evalC` | `/work/gdp-wired/base/core/machine.ts` |
| 3.9% | 16.06s | 3.9% | 16.06s | `stringify` | `[native code]` |
| 3.6% | 14.73s | 3.6% | 14.73s | `(anonymous)` | `/work/gdp-wired/base/core/machine.ts` |
| 3.0% | 12.43s | 40.4% | 164.08s | `some` | `[native code]` |
| 3.0% | 12.26s | 31.4% | 127.63s | `at` | `/work/gdp-wired/base/core/machine.ts:488` |
| 2.8% | 11.54s | 8.0% | 32.60s | `evalE` | `/work/gdp-wired/base/core/machine.ts:350` |
| 2.7% | 11.33s | 69.8% | 283.45s | `go` | `/work/gdp-wired/base/core/machine.ts:499` |
| 2.6% | 10.76s | 24.7% | 100.52s | `evalC` | `/work/gdp-wired/base/core/machine.ts:399` |
| 2.3% | 9.61s | 2.3% | 9.61s | `evalC` | `/work/gdp-wired/base/core/machine.ts:402` |
| 1.8% | 7.52s | 23.5% | 95.56s | `every` | `[native code]` |
| 1.7% | 7.14s | 41.1% | 166.89s | `evalC` | `/work/gdp-wired/base/core/machine.ts:400` |
| 1.7% | 7.00s | 1.7% | 7.00s | `evalE` | `/work/gdp-wired/base/core/machine.ts` |
| 1.1% | 4.67s | 1.1% | 4.67s | `at` | `/work/gdp-wired/base/core/machine.ts` |
| 1.1% | 4.51s | 3.6% | 14.72s | `reads` | `/work/gdp-wired/base/core/machine.ts:522` |
| 1.0% | 4.42s | 1.0% | 4.42s | `crossFree` | `/work/gdp-wired/base/kernel/kernel.ts:687` |
| 0.8% | 3.63s | 6.0% | 24.41s | `evalC` | `/work/gdp-wired/base/core/machine.ts:397` |
| 0.8% | 3.57s | 0.8% | 3.57s | `evalE` | `/work/gdp-wired/base/core/machine.ts:340` |
| 0.8% | 3.49s | 4.3% | 17.62s | `evalE` | `/work/gdp-wired/base/core/machine.ts:355` |
| 0.7% | 3.05s | 0.7% | 3.05s | `values` | `[native code]` |
| 0.6% | 2.75s | 1.2% | 5.17s | `evalC` | `/work/gdp-wired/base/core/machine.ts:401` |
| 0.4% | 2.01s | 16.2% | 66.13s | `forEach` | `[native code]` |
