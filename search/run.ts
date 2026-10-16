import {required, runPage} from '../vendor/handwired/lab/json-search/gpu/chrome.ts'
import page from './page.html'
await runPage({page, config: {}, label: 'search', profile: required('--profile'), out: required('--out'), port: 4436, devToolsPort: 9436, timeoutMs: 1_200_000,
  chromePath: '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome'})
