// Repro: golang.org/x/time v0.16.0 (the pinned commit fb013b3d305a26f5ef5350a6eaffc7c87a200383), Limiter.AllowN with a
// time that goes back: the run gdp-wired's search found for "no more is granted than burst plus rate times the latest
// time seen". params {rate: 1 per second, burst: 3}; AllowN at t = 0 s (n 2), 3 s (n 2), 1 s (n 0), 2 s (n 3), 1 s (n 0),
// 3 s (n 3). reserveN sets lim.last = t even when t is before lim.last (rate.go:378), so the tokens for [1 s, 3 s] are
// credited a second time: 7 events granted by t = 3 s against burst + rate * 3 s = 6. Times that go back at the lock are
// what concurrent callers of Allow() (each reading time.Now() before taking the mutex) send: golang/go#65508 (open)
// reports the same over-admission from this line. Writes a Go module into a temp dir and runs it.
//   bun research/realworld/repro/go-rate-backwards.ts                  (needs go and network for the module)
import {execFileSync} from 'node:child_process'
import {mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'

const dir = mkdtempSync(join(tmpdir(), 'go-rate-repro-'))
writeFileSync(join(dir, 'go.mod'), 'module repro\n\ngo 1.26\n\nrequire golang.org/x/time v0.16.0\n')
writeFileSync(join(dir, 'main.go'), `package main

import (
	"fmt"
	"time"

	"golang.org/x/time/rate"
)

func main() {
	base := time.Unix(1_700_000_000, 0)
	lim := rate.NewLimiter(1, 3)
	granted := 0
	for _, s := range []struct{ t, n int }{{0, 2}, {3, 2}, {1, 0}, {2, 3}, {1, 0}, {3, 3}} {
		ok := lim.AllowN(base.Add(time.Duration(s.t)*time.Second), s.n)
		if ok {
			granted += s.n
		}
		fmt.Printf("AllowN(t=%ds, n=%d) = %v, granted so far %d\\n", s.t, s.n, ok, granted)
	}
	fmt.Printf("granted %d events by t = 3s; burst + rate * 3s = %d\\n", granted, 3+1*3)
	// Control: the same calls with t never going back (the two t = 1s calls at 3s):
	lim2, g2 := rate.NewLimiter(1, 3), 0
	for _, s := range []struct{ t, n int }{{0, 2}, {3, 2}, {3, 0}, {3, 3}, {3, 0}, {3, 3}} {
		if lim2.AllowN(base.Add(time.Duration(s.t)*time.Second), s.n) {
			g2 += s.n
		}
	}
	fmt.Printf("control, time never going back: granted %d\\n", g2)
}
`)
execFileSync('go', ['mod', 'tidy'], {cwd: dir, stdio: 'inherit', env: {...process.env, GOFLAGS: '-mod=mod'}})
console.log(execFileSync('go', ['run', '.'], {cwd: dir, encoding: 'utf8'}))
