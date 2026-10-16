# gdp-wired modal-gpu: Handwired's GPU searches on Modal GPUs

| File | What |
| --- | --- |
| `suite.ts` | The search suite on whatever `navigator.gpu` gives, with Handwired's `host.ts` (`requestBatchDevice`, `createKernelRunner`) and `search/compile.ts`'s shaders. Spaces past 2^31 candidates run in slices: the low digits are the dispatch index, the high digits (the last steps' requests) come from `tables[2]` (one injected line in the shader). Every counterexample is replayed by the interpreter |
| `dawn-run.ts` | The suite without a browser: Dawn's node bindings (`webgpu@0.6.2`) as `navigator.gpu`, Vulkan on Linux, Metal on a Mac |
| `gpu-page.ts`, `gpu-page.html`, `driver.ts` | The same suite in headless Chrome, with a Linux driver instead of Handwired's macOS-only `runPage` |
| `run_gpu.py` | Modal: debian + NVIDIA Vulkan loader libs (libvulkan1, libxext6, libx11-6, libglvnd0, libegl1) + Chrome + bun + `webgpu`; `--gpu L4/A10G/H100`, `--mode dawn/chrome`; 15-minute timeout; the call is cancelled if the client stops |
| `suite.json`, `suite-big.json` | The searches of `search/models.ts`, depth 9, and larger spaces (depth 10–12, bound 3) |
| `probe.py`, `probe2.py`, `probe-chrome.ts`, `probe-dawn.ts` | How the setup was found: Vulkan on the container, Chrome flag sets, Dawn |

Findings: Modal mounts NVIDIA's Vulkan ICD (`/etc/vulkan/icd.d/nvidia_icd.json`), which needs libXext to load. Dawn then
gets the real GPU. Chrome 155 on the same container only ever offers SwiftShader (7 flag sets tried), so Dawn is the path.

Results (`../runs/modal/gpu-search/`, gpuMs after a warm-up for the first five rows; M2 is Chrome on the Mac):

| Search | Candidates | M2 | L4 | H100 |
| --- | --- | --- | --- | --- |
| admit, Day unguarded | 268M | 154 ms | 41.8 ms | 17.9 ms |
| in-flight b+4 (depth-6 counterexample) | 129M | 36.6 ms | 6.3 ms | 3.2 ms |
| in-flight b+5 | 129M | 35.9 ms | 6.3 ms | 2.9 ms |
| in-flight b+5, depth 9 | 1.16B | 327 ms | 48.5 ms | 23.3 ms |
| uncapped | 2.1M | 0.47 ms | 0.40 ms | 0.25 ms |
| in-flight b+5, depth 10 | 10.5B | — | 424 ms | 203 ms |
| in-flight b+4, depth 10 | 10.5B | — | 428 ms (same counterexample) | 200 ms |
| in-flight b+5, depth 11 | 94.1B | — | 3.84 s | 1.80 s |
| in-flight b+5, bound 3, depth 8 | 17.2B | — | 444 ms | 230 ms |
| in-flight b+5, depth 12 | 847B | — | — | 16.1 s |

```sh
cd gdp-wired && modal run modal-gpu/run_gpu.py --config modal-gpu/suite.json --out ../runs/modal/gpu-search/l4.json --gpu L4
# locally, on the Mac's GPU through Dawn (webgpu installed under ../runs/dawn-local):
cd modal-gpu && DAWN_MODULE=$PWD/../runs/dawn-local/node_modules/webgpu/index.js bun dawn-run.ts --config "$(cat suite.json)" --out local.json
```
The apps are named `hw-gpu-*`. (`modal/reap.sh` now stops only runs whose client died, so it is safe either way; it
doesn't know about GPU runs.) After a run: `modal app list`, and `modal app stop -y <id>` for anything left.
