// The `webgpu` npm package (Dawn's node bindings), installed only where the GPU runs are made (research/modal-gpu/, research/hw/).
declare module 'webgpu' {
  export const globals: Record<string, unknown>
  export function create(options: string[]): GPU
}
