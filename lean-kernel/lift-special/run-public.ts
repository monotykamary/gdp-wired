// Public command adapter integration only: no protocol registry/search/replay.
import {liftMain} from '../../core/lift-cli.ts'
process.exitCode=await liftMain(process.argv.slice(2))
