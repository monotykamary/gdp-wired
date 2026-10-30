#!/usr/bin/env node
// gdp-wired's command line (core/cli.ts) with TypeScript installed beside it: every front end reads a rule through the
// TypeScript extractor's terms, so `npx gdp-wired-cli check <file|dir>` needs nothing else. Its version is gdp-wired's.
import {main} from 'gdp-wired/cli'

main(process.argv.slice(2)).then(c => { process.exitCode = c }, e => { process.stdout.write(`gdp-wired-cli: ${e instanceof Error ? e.message : String(e)}\n`); process.exitCode = 2 })
