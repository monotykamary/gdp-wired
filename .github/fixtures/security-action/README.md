# Security Action fixture repository

The workflow copies these original synthetic sources into a temporary Git repository.
`candidate.ts` intentionally generates a broken authorization *candidate*: review is
required and its exit code must remain zero. `stated-broken.ts` states that requirement
as a `gdp: law`; it must fail with exit 1. No third-party source or deployment is used.
