# Artifact handling for future reruns

This directory preserves the completed historical gate manifests and receipts.
The old strict28 input driver emitted compressed receipt bodies in stdout;
that is an archival record, NOT an approved pattern for another job.

For every future supercomputer run, put proof/receipt payloads in job output
files and fetch them as files. Job result stdout/JSON must contain only small
summaries, hashes and output paths, never base64 or bulk file contents. Do not
rerun the historical default-model driver unchanged. The cap/native/endpoint
records here are bounded scalar summaries, not embedded proof bodies.
