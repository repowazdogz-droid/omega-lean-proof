# NOT A SHIPPED ROOT

Files here are recon / scratch only. They are **not** Lake build roots and must not
be imported by `OmegaP3Semantic` or any other shipped module until explicitly promoted.

## Run JCS conformance probe

```bash
cd lean-proof/scratch
npm install   # pins canonicalize@3.0.0
node jcs-conformance-test.mjs | tee jcs-conformance-results.json
```

Official test vectors are vendored under `jcs-testdata/` (from
[cyberphone/json-canonicalization](https://github.com/cyberphone/json-canonicalization)).
