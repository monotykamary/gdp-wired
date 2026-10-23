// Repro (from the source) for queue/pg-boss/retry, law 'a job is claimed at most retryLimit + 1 times'.
// The code runs in Postgres; this harness reasons from the SQL at the pinned commit (pg-boss 12.38.0,
// 2c1005b744952360e999c2000e155a1bfebb8951) and prints the statements it rests on, fetched from GitHub.
//
// The rule's run (retry_limit 0): fetch, cancel, resume, fetch.
//   1. fetchNextJob (plans.ts:2813-2817): state active, started_on = now, retry_count stays 0 (started_on was null).
//   2. cancelJobs (:2986-3009): `state < 'completed'`, so active -> cancelled.
//   3. resumeJobs (:3011-3035): cancelled -> created; started_on is not cleared.
//   4. fetchNextJob again: `state < 'active' AND start_after <= job_now()` holds, and since started_on is not null,
//      `retry_count = retry_count + 1`: the job runs a second time with retry_count 1 > retry_limit 0.
// So the original does it. The intent (docs/api/jobs.md:33-35 "retryLimit ... Number of retries to complete a job") is
// about automatic retries; resume() is a deliberate re-run by hand. Verdict: a law error; the law was restated as
// 'without a resume, a job is claimed at most retryLimit + 1 times'. `bun research/realworld/repro/pg-boss-resume.ts`
export {}
const at = 'https://raw.githubusercontent.com/timgit/pg-boss/2c1005b744952360e999c2000e155a1bfebb8951/src/plans.ts'
const lines = (await (await fetch(at)).text()).split('\n')
for (const [from, to] of [[2813, 2817], [2986, 2996], [3011, 3030]] as const) {
  console.log(`plans.ts:${from}-${to}`)
  for (let i = from; i <= to; i++) console.log(`  ${i}  ${lines[i - 1]}`)
}
