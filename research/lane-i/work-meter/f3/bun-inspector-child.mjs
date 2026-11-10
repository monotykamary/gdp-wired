await new Promise(resolve => setTimeout(resolve, 500))
function mainThreadSilentLoop() {
  process.stdout.write('LOOP_ENTER\n')
  const end = performance.now() + 4000
  let value = 0
  while (performance.now() < end) value = (value + 1) >>> 0
  process.stdout.write('LOOP_DONE ' + value + '\n')
}
mainThreadSilentLoop()
