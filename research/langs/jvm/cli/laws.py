# resilience4j's PartialAggregation laws of specs.ts written as `// gdp: law` comments in its own Java (a copy: the
# comments only). `python3 laws.py <PartialAggregation.java>`, then `npx gdp-wired check <PartialAggregation.java>`.
import pathlib, re, sys

p = pathlib.Path(sys.argv[1])
M = "2147483647"
CLASS = [
    f"record counts one call: method == \"record\" and old(numberOfCalls) < {M} implies numberOfCalls == old(numberOfCalls) + 1",
    f"a slow error is slow, failed and slow failed: outcome == SLOW_ERROR and old(numberOfSlowCalls) < {M} and old(numberOfFailedCalls) < {M} and old(numberOfSlowFailedCalls) < {M} implies numberOfSlowCalls == old(numberOfSlowCalls) + 1 and numberOfFailedCalls == old(numberOfFailedCalls) + 1 and numberOfSlowFailedCalls == old(numberOfSlowFailedCalls) + 1",
    "a success counts nothing but the call: outcome == SUCCESS implies numberOfSlowCalls == old(numberOfSlowCalls) and numberOfFailedCalls == old(numberOfFailedCalls) and numberOfSlowFailedCalls == old(numberOfSlowFailedCalls)",
    "record adds a millisecond duration as it is: durationUnit == MILLISECONDS implies totalDurationInMillis == old(totalDurationInMillis) + duration",
    "slow failed calls never outnumber slow calls: numberOfSlowFailedCalls <= numberOfSlowCalls",
]
RESET = ["reset zeroes every count and starts the epoch: this.epochSecond == epochSecond and totalDurationInMillis == 0 and numberOfCalls == 0 and numberOfSlowCalls == 0 and numberOfFailedCalls == 0 and numberOfSlowFailedCalls == 0"]
lines = p.read_text().split("\n")
i = next(k for k, l in enumerate(lines) if re.search(r"\bvoid\s+reset\s*\(", l))
lines[i:i] = [f"    // gdp: law {l}" for l in RESET]
i = next(k for k, l in enumerate(lines) if re.search(r"\bclass\s+PartialAggregation\b", l))
lines[i + 1:i + 1] = [f"    // gdp: law {l}" for l in CLASS]
p.write_text("\n".join(lines))
print("laws:", len(CLASS) + len(RESET))
