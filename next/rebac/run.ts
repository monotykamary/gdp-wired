import {required, runPage} from '../../vendor/handwired/lab/json-search/gpu/chrome.ts'
import page from './page.html'
await runPage({page, config: {counts: [10_000, 100_000, 1_000_000]}, label: 'rebac', profile: required('--profile'), out: required('--out'), port: 4435, devToolsPort: 9435, timeoutMs: 1_200_000,
  chromePath: '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome'})
