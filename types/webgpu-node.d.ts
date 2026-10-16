// The `webgpu` npm package (Dawn's node bindings), installed only where the GPU runs are made (modal-gpu/, hw/).
declare module 'webgpu' {
  export const globals: Record<string, unknown>
  export function create(options: string[]): GPU
}
