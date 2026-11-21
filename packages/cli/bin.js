#!/usr/bin/env node
// gdp-wired's command line (core/cli.ts) with TypeScript installed beside it: every front end reads a rule through the
// TypeScript extractor's terms, so `npx gdp-wired-cli check <file|dir>` needs nothing else. Its version is gdp-wired's.
import {runCli} from 'gdp-wired/cli'

runCli(process.argv.slice(2), {label: 'gdp-wired-cli'})
