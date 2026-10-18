// Dawn's node bindings (the `webgpu` npm package) as navigator.gpu, without a browser.
import {create, globals} from 'webgpu'
Object.assign(globalThis, globals)
const gpu = create(['backend=vulkan'])
const a = await gpu.requestAdapter({powerPreference: 'high-performance'})
console.log(a ? JSON.stringify({vendor: a.info.vendor, architecture: a.info.architecture, description: a.info.description, maxBuf: a.limits.maxStorageBufferBindingSize}) : 'null adapter')
