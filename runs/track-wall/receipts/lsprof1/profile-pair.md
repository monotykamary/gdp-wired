model name	: AMD Ryzen 9 9950X 16-Core Processor
SIDE mine
[infer runs] {"samples":3000,"trials":0}
[infer] runs {"ms":4,"counted":0,"work":0,"tries":0,"rows":0,"evals":0,"watched":0,"erows":0,"etries":0,"samples":3000,"trials":0}
[infer join small domains] {"params":"{\"size\":3}","doms":"op:0/1/2 ps:0/1/2 pd:0/1/2 sw0:0/1/2 sw1:0/1/2 nondet:0/1/2","combos":729}
[infer join small instance] {"states":6011,"bfs":478,"params":1,"symmetric":"","ms":1502,"took":1502}
{"id":"learning_switch","count":16,"wallMs":221045.013404,"phases":{"guards":6.751276000000004,"small":216540.39083000002,"candidates":4491.264217999997},"states":[750,3420],"counts":[],"cprof":{"small":0.014727999980095774,"cubes":4020.4830920000095,"filter":459.8699889999989,"quorumFilter":0.00630
PROFILE
**Top 10:** `fromEntries` 9.1%, `go` 7.5%, `map` 6.4%, `copyDataProperties` 6.4%, `evalC` 6.1%, `cloneObject` 5.5%, `(anonymous)` 4.6%, `(anonymous)` 4.0%, `some` 3.8%, `evalE` 3.7%
| 9.1% | 20.18s | 9.3% | 20.56s | `fromEntries` | `[native code]` |
| 7.5% | 16.64s | 100.0% | 708.66s | `go` | `/work/gdp-wired/core/machine.ts:498` |
| 6.4% | 14.33s | 100.0% | 497.43s | `map` | `[native code]` |
| 6.4% | 14.28s | 6.4% | 14.28s | `copyDataProperties` | `[native code]` |
| 6.1% | 13.49s | 6.1% | 13.49s | `evalC` | `/work/gdp-wired/core/machine.ts:395` |
| 5.5% | 12.16s | 5.5% | 12.16s | `cloneObject` | `[native code]` |
| 4.6% | 10.33s | 4.6% | 10.33s | `(anonymous)` | `/work/gdp-wired/core/machine.ts:488` |
| 4.0% | 9.00s | 4.0% | 9.00s | `(anonymous)` | `/work/gdp-wired/core/machine.ts` |
| 3.8% | 8.51s | 45.9% | 101.53s | `some` | `[native code]` |
| 3.7% | 8.22s | 11.5% | 25.43s | `evalE` | `/work/gdp-wired/core/machine.ts:350` |
| 3.3% | 7.35s | 3.3% | 7.35s | `evalC` | `/work/gdp-wired/core/machine.ts` |
| 3.3% | 7.34s | 3.3% | 7.34s | `stringify` | `[native code]` |
| 3.1% | 6.91s | 33.8% | 74.88s | `at` | `/work/gdp-wired/core/machine.ts:488` |
| 2.7% | 6.16s | 2.7% | 6.16s | `evalC` | `/work/gdp-wired/core/machine.ts:402` |
| 2.7% | 6.14s | 2.7% | 6.15s | `evalE` | `/work/gdp-wired/core/machine.ts` |
| 2.6% | 5.87s | 72.3% | 159.89s | `go` | `/work/gdp-wired/core/machine.ts:499` |
| 1.8% | 4.14s | 28.3% | 62.58s | `every` | `[native code]` |
| 1.5% | 3.36s | 28.3% | 62.59s | `evalC` | `/work/gdp-wired/core/machine.ts:399` |
| 1.3% | 3.07s | 4.0% | 9.01s | `reads` | `/work/gdp-wired/core/machine.ts:522` |
| 1.2% | 2.81s | 1.2% | 2.81s | `evalE` | `/work/gdp-wired/core/machine.ts:340` |
| 1.1% | 2.54s | 1.1% | 2.54s | `crossFree` | `/work/gdp-wired/kernel/kernel.ts:687` |
| 1.0% | 2.42s | 45.9% | 101.67s | `evalC` | `/work/gdp-wired/core/machine.ts:400` |
| 1.0% | 2.41s | 7.9% | 17.50s | `evalC` | `/work/gdp-wired/core/machine.ts:397` |
| 1.0% | 2.26s | 6.2% | 13.79s | `evalE` | `/work/gdp-wired/core/machine.ts:355` |
| 0.9% | 2.05s | 0.9% | 2.05s | `at` | `/work/gdp-wired/core/machine.ts` |
| 0.7% | 1.69s | 0.7% | 1.69s | `values` | `[native code]` |
| 0.6% | 1.35s | 0.6% | 1.35s | `(anonymous)` | `/work/gdp-wired/core/machine.ts:522` |
| 0.5% | 1.19s | 1.2% | 2.84s | `evalC` | `/work/gdp-wired/core/machine.ts:401` |
SIDE base
[infer runs] {"samples":3000,"trials":0}
[infer] runs {"ms":10,"counted":0,"work":0,"tries":0,"rows":0,"evals":0,"watched":0,"erows":0,"etries":0,"samples":3000,"trials":0}
[infer join small domains] {"params":"{\"size\":3}","doms":"op:0/1/2 ps:0/1/2 pd:0/1/2 sw0:0/1/2 sw1:0/1/2 nondet:0/1/2","combos":729}
[infer join small instance] {"states":6011,"bfs":478,"params":1,"symmetric":"","ms":1502,"took":1502}
{"id":"learning_switch","count":16,"wallMs":216142.702877,"phases":{"guards":2.36774299999999,"small":210844.599573,"candidates":5282.265688999993},"states":[750,3420],"counts":[],"cprof":{"small":0.0345450000022538,"cubes":4894.480142999993,"filter":361.5171580000315,"quorumFilter":0.00920800000312
PROFILE
**Top 10:** `fromEntries` 9.1%, `go` 7.7%, `evalC` 7.4%, `copyDataProperties` 7.0%, `(anonymous)` 6.0%, `map` 5.9%, `cloneObject` 5.3%, `(anonymous)` 4.3%, `some` 3.5%, `stringify` 3.3%
| 9.1% | 19.80s | 9.2% | 20.07s | `fromEntries` | `[native code]` |
| 7.7% | 16.73s | 100.0% | 696.18s | `go` | `/work/gdp-wired/base/core/machine.ts:498` |
| 7.4% | 16.15s | 7.4% | 16.15s | `evalC` | `/work/gdp-wired/base/core/machine.ts:395` |
| 7.0% | 15.27s | 7.0% | 15.27s | `copyDataProperties` | `[native code]` |
| 6.0% | 13.02s | 6.0% | 13.02s | `(anonymous)` | `/work/gdp-wired/base/core/machine.ts` |
| 5.9% | 12.80s | 100.0% | 487.36s | `map` | `[native code]` |
| 5.3% | 11.51s | 5.3% | 11.51s | `cloneObject` | `[native code]` |
| 4.3% | 9.36s | 4.3% | 9.36s | `(anonymous)` | `/work/gdp-wired/base/core/machine.ts:488` |
| 3.5% | 7.61s | 46.4% | 100.52s | `some` | `[native code]` |
| 3.3% | 7.18s | 3.3% | 7.18s | `stringify` | `[native code]` |
| 2.9% | 6.37s | 10.0% | 21.81s | `evalE` | `/work/gdp-wired/base/core/machine.ts:350` |
| 2.9% | 6.30s | 33.7% | 72.95s | `at` | `/work/gdp-wired/base/core/machine.ts:488` |
| 2.8% | 6.15s | 2.8% | 6.15s | `evalE` | `/work/gdp-wired/base/core/machine.ts` |
| 2.6% | 5.81s | 72.2% | 156.28s | `go` | `/work/gdp-wired/base/core/machine.ts:499` |
| 2.6% | 5.77s | 2.6% | 5.77s | `evalC` | `/work/gdp-wired/base/core/machine.ts` |
| 2.3% | 5.12s | 31.0% | 67.18s | `evalC` | `/work/gdp-wired/base/core/machine.ts:399` |
| 2.0% | 4.44s | 29.9% | 64.84s | `every` | `[native code]` |
| 1.2% | 2.79s | 3.8% | 8.34s | `reads` | `/work/gdp-wired/base/core/machine.ts:522` |
| 1.1% | 2.55s | 46.7% | 101.05s | `evalC` | `/work/gdp-wired/base/core/machine.ts:400` |
| 1.1% | 2.55s | 1.1% | 2.55s | `evalC` | `/work/gdp-wired/base/core/machine.ts:402` |
| 1.1% | 2.54s | 1.1% | 2.54s | `crossFree` | `/work/gdp-wired/base/kernel/kernel.ts:687` |
| 1.0% | 2.30s | 1.0% | 2.30s | `evalE` | `/work/gdp-wired/base/core/machine.ts:340` |
| 0.8% | 1.86s | 0.8% | 1.86s | `at` | `/work/gdp-wired/base/core/machine.ts` |
| 0.8% | 1.86s | 5.7% | 12.41s | `evalE` | `/work/gdp-wired/base/core/machine.ts:355` |
| 0.7% | 1.64s | 0.7% | 1.64s | `values` | `[native code]` |
| 0.6% | 1.50s | 0.7% | 1.51s | `crossFree` | `/work/gdp-wired/base/kernel/kernel.ts:694` |
| 0.6% | 1.35s | 6.8% | 14.88s | `evalC` | `/work/gdp-wired/base/core/machine.ts:397` |
| 0.5% | 1.15s | 0.5% | 1.15s | `evalE` | `/work/gdp-wired/base/core/machine.ts:341` |
