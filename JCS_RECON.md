# JCS_RECON — Phase 2 bridge: Lean proof model ↔ production RFC 8785 (JCS)

**Date:** 2026-06-09  
**Scope:** Read-only recon. No changes to shipped Lean roots, `SPEC.md`, or site.  
**Scratch harness:** `lean-proof/scratch/jcs-conformance-test.mjs` (not a shipped root)

---

## Executive summary

| Question | Finding |
|---|---|
| Does production `canonicalize@3.0.0` pass official RFC 8785 vectors? | **YES — 6/6 pass** (cyberphone testdata) |
| UTF-16 code-unit key sort | Package uses `Object.keys().sort()` → **UTF-16 code units** (matches RFC on tested vectors including `french.json`, `weird.json`) |
| Do current omega-contracts records need non-integer JSON numbers? | **YES — 72 non-integer values** in fixtures (scores/ratios/confidence 0–1). Integer-only subset **violates current schema + fixtures** without migration |
| Do demo refund records need floats? | **NO** — `omega-demo/examples/refund-escalation.json` uses integers only; uses non-ASCII em-dash in strings |
| Recommended Phase 2 route | **OMEGA JCS profile** (normative subset + empirical conformance bridge), not full IEEE-754 formalization |
| Estimated effort | Full JCS in Lean: **6+ months**. Profile + Lean encoder + corpus bridge: **~3 weeks** first milestone |

**No production RFC conformance bug found** in this recon. The npm package is a thin wrapper around `JSON.stringify` + `Object.keys().sort()`; it passes all official vectors run here. The Lean gap is architectural (binary tuple model vs JCS text), not a detected npm deviation.

---

## Step 1 — Runtime canonicalizer ground truth

### 1.1 Package resolution (omega-contracts)

| Field | Value |
|---|---|
| Package | `canonicalize` |
| Requested | `^3.0.0` (`omega-contracts/package.json`) |
| **Resolved** | **`3.0.0`** |
| Integrity | `sha512-yYLfHyDMIXRyRqsKBRLX023riFLpXY2YOfdtqKXZRZy9qsfOJ9U+4F9YZL7MEzL5+ziN2x2nlBvY/Voi3EBljA==` |
| Lockfile | `omega-contracts/package-lock.json` → `node_modules/canonicalize` |
| Upstream | [erdtman/canonicalize](https://github.com/erdtman/canonicalize) (co-maintained with JCS author Anders Rundgren) |
| Wiring | `omega-contracts/src/encoding.ts` re-exports default export; `computeContentHash` SHA-256s UTF-8 bytes |

### 1.2 Source (verbatim — full implementation, 49 lines)

The production canonicalizer is **not** a standalone JCS engine. Primitives delegate to
`JSON.stringify`; object keys use lexicographic `Array.prototype.sort()` (UTF-16 code units).

```javascript
export default function canonicalize (object, seen = new Set()) {
  if (typeof object === 'number' && isNaN(object)) {
    throw new Error('NaN is not allowed');
  }

  if (typeof object === 'number' && !isFinite(object)) {
    throw new Error('Infinity is not allowed');
  }

  if (object === null || typeof object !== 'object') {
    return JSON.stringify(object);
  }

  if (typeof object.toJSON === 'function') {
    if (seen.has(object)) {
      throw new Error('Circular reference detected');
    }
    seen.add(object);
    const result = canonicalize(object.toJSON(), seen);
    seen.delete(object);
    return result;
  }

  if (seen.has(object)) {
    throw new Error('Circular reference detected');
  }
  seen.add(object);

  let result;
  if (Array.isArray(object)) {
    const values = object.map((cv) => {
      const value = cv === undefined || typeof cv === 'symbol' ? null : cv;
      return canonicalize(value, seen);
    });
    result = `[${values.join(',')}]`;
  } else {
    const parts = [];
    for (const key of Object.keys(object).sort()) {
      if (object[key] === undefined || typeof object[key] === 'symbol') {
        continue;
      }
      parts.push(`${canonicalize(key)}:${canonicalize(object[key], seen)}`);
    }
    result = `{${parts.join(',')}}`;
  }

  seen.delete(object);
  return result;
}
```

**Implications:**
- **Key sorting:** `Object.keys(object).sort()` — default string comparator, **UTF-16 code unit order** (ECMAScript `CompareStrings`).
- **Numbers:** `JSON.stringify` → V8 `NumberToString` (shortest round-trip, ES6 rules).
- **Strings:** `JSON.stringify` escape rules (`\uXXXX` uppercase for controls; lone surrogates escaped as `\uD800` etc.).
- **Omissions:** `undefined` and `Symbol` property values skipped; array `undefined`/`Symbol` → `null`.
- **Rejected:** `NaN`, `±Infinity`; circular references throw.

### 1.3 Official RFC 8785 test vectors (cyberphone/json-canonicalization)

Source: `https://github.com/cyberphone/json-canonicalization/tree/master/testdata`  
Vendored: `lean-proof/scratch/jcs-testdata/`  
Runner: `node lean-proof/scratch/jcs-conformance-test.mjs`

#### Vector results

| Vector | Pass | Expected (decoded) | Got | Notes |
|---|---|---|---|---|
| `arrays.json` | **PASS** | `[56,{"1":[],"10":null,"d":true}]` | identical | Top-level array; nested object key sort `1` < `10` |
| `french.json` | **PASS** | `{"peach":"…","péché":"…","pêche":"…","sin":"…"}` | identical | Locale must not affect order; default sort ≠ `localeCompare('fr')` here |
| `structures.json` | **PASS** | (RFC crazy example) | identical | Empty string key, `\n` in key, nested objects |
| `unicode.json` | **PASS** | `{"Unnormalized Unicode":"Å"}` | identical | NFC vs NFD — output preserves input code unit sequence |
| `values.json` | **PASS** | numbers + escapes + literals | identical | See number/string probes below |
| `weird.json` | **PASS** | keys: `\n`, `\r`, `1`, `</script>`, `€`, `😂`, Hebrew דּ, etc. | identical | **Strong UTF-16 / non-ASCII key test** |

**Gate: 6/6 PASS — no production RFC conformance bug flagged.**

Full machine output: `lean-proof/scratch/jcs-conformance-results.json` → `officialVectors`.

### 1.4 Targeted probes (Step 1a–c)

#### (a) UTF-16 code-unit key sorting

| Probe | Result |
|---|---|
| `french.json` official vector | PASS — order `peach`, `péché`, `pêche`, `sin` |
| `defaultSort` vs `localeCompare('fr')` on french keys | **Same order** (this dataset) |
| Supplementary vs BMP (`\u0100` vs U+1D400 `𝐀`) | Both orders agree; JS `.sort()` = UTF-16 code units |
| `weird.json` (emoji, Hebrew, euro as keys) | PASS |

**Watch item for Lean:** Lean 4 `String` ordering compares **Unicode scalar values (code points)**, not UTF-16 code units. For keys containing surrogate pairs or **lone surrogates**, Lean sort **may diverge** from JCS. Production npm + JSON.parse typically produce valid UTF-16 strings; the `weird.json` vector includes emoji (valid surrogate pair). **Lean needs an explicit UTF-16 code-unit comparator** for object keys.

#### (b) Number serialization

| Input | `JSON.stringify` / `canonicalize` | RFC notes |
|---|---|---|
| `1e21` | `1e+21` | PASS |
| `1e-7` | `1e-7` | PASS |
| `0.1 + 0.2` | `0.30000000000000004` | Honest ES double — not decimal 0.3 |
| `-0` | `0` | `-0` canonicalizes as `0` |
| `9007199254740993` | `9007199254740992` | **Precision loss** — JSON.parse / JS number already rounded |
| `333333333.33333329` | `333333333.3333333` | Matches `values.json` vector |
| `1E30` | `1e+30` | PASS |
| `4.50` | `4.5` | Trailing zero dropped |
| `2e-3` | `0.002` | Normalized decimal form |
| `1e-27` | `1e-27` | PASS |

**Lean implication:** reproducing production hashes for records with float scores requires either (1) formal IEEE-754 shortest printing, or (2) **excluding non-integer numbers** from the normative subset, or (3) **empirical conformance only** for float fields via generated corpus (recommended interim).

#### (c) String escaping

| Input | Output | Behavior |
|---|---|---|
| U+001F | `"\u001f"` | Control escaped, **lowercase** hex |
| `\n`, `\r` | `"\n"`, `"\r"` | Named escapes |
| `"`, `\`, `/` | escaped | PASS |
| U+20AC euro | `"€"` | UTF-8 in output string; unescaped BMP |
| Lone `\uD800`, `\uDC00` | `"\ud800"`, `"\udc00"` | **Passed through** as escaped lone surrogates (no throw) |
| Lone surrogate as key | `{"\ud800":"lonely"}` | PASS |

### 1.5 Composition hash sanity check

| | Value |
|---|---|
| `computeContentHash(expected_record.json)` | `152eab926412e397dfdd56217dad03a924bc9c138bee2ceafa2f3200c3d2c705` |
| `fixtures/composition/expected_content_hash.txt` | **match** |

---

## Step 2 — OmegaRecord value-domain audit

### 2.1 Sources scanned

| Source | Files |
|---|---|
| `omega-contracts/fixtures/**` | 18 JSON files (all protocol natives + canonical expected + composition) |
| `omega-contracts/test/**` | JSON embedded in tests (specgap fingerprint vector) |
| `omega-contracts-spec/SPEC.md` | Schema prose (§7, §8, score semantics) |
| `omega-contracts/schemas/*.json` | JSON Schema types |
| `omega-demo/examples/*.json` | **Manual review** (not in omega-contracts; demo envelope) |

### 2.2 Automated scan summary (`jcs-conformance-test.mjs`)

| Metric | Value |
|---|---|
| Files scanned | 18 JSON under `omega-contracts/fixtures/` + test fixtures |
| **Non-integer numbers** | **72** |
| Integers outside ±(2⁵³−1) | **0** |
| Non-ASCII string values | **0** |
| Non-ASCII object keys | **0** |
| Arrays present | **yes** (throughout protocol natives, composition inputs, trust evidence) |
| Max nesting depth | **8** |
| null / boolean | yes |

**Non-integer locations (pattern):** scores, ratios, confidence, weights in
`trust-score`, `clearpath`, `cognitive`, `harm`, `assumption`, `dispute`, `ethics`
canonical fixtures — e.g. `0.76`, `0.18`, `0.72`, `assumption_ratio`-style floats.

Example non-integer paths (sample):

```
fixtures/trust-score/canonical.expected.json."overall_score" → 0.76
fixtures/clearpath/canonical.expected.json."assumption_ratio" → (float|null)
fixtures/composition/expected_record.json → trust dimension scores (floats)
```

### 2.3 omega-demo examples (manual)

| File | Numbers | Strings | Notes |
|---|---|---|---|
| `refund-escalation.json` | **All integers** (`2500`, `4820`, `120`) | ASCII + **U+2014 em dash** in `delegation` | Extra fields (`authority`, `evidence`, `confirmation`) — **not** in current `OmegaRecord` schema |
| `delegation-escalation.json` | All integers | ASCII | Same demo envelope |

Demo records are **integer-clean** but **schema-heterogeneous** (demo-only fields). They are **not** the same shape as `fixtures/composition/expected_record.json`.

### 2.4 SPEC.md constraints today

**§7 — Canonical encoding and hashing** (quoted):

> **Canonical form.** `content_hash` MUST be computed over the RFC 8785 JSON Canonicalization Scheme (JCS) output of the `OmegaRecord` with `content_hash` and `signature` fields omitted.
>
> **Hash algorithm.** SHA-256.
>
> **Hash format.** Lowercase hex string. No prefix. 64 characters.

**Absent from SPEC:** any restriction that JSON numbers MUST be integers, any
Unicode normalization policy, maximum nesting depth, or array prohibition.

**§8 score semantics** explicitly define **0–1 floating scores** (`assumption_ratio`,
`calibration`, `consistency`, `max_severity`, `TrustScore.overall_score`, etc.) and
JSON Schema uses bare `"type": "number"` throughout — **non-integer numbers are
first-class by design**.

**§I-3:** numeric scores declare range and direction — implies continuous ratios, not integers only.

---

## Step 3 — Scope recommendation

### 3.1 Full JCS formalization (not recommended for Phase 2)

Formalizing complete RFC 8785 in Lean requires:

1. IEEE 754 double → shortest decimal/exponent string (Ryū-style) — **single hardest piece**
2. Full escape table + UTF-8 output bytes
3. UTF-16 code-unit key ordering
4. Decoder totality for all JCS outputs

**Estimate:** 6+ months specialist effort. Mathlib has limited JSON/JCS infrastructure.

### 3.2 OMEGA JCS profile (recommended)

Define **OMEGA Canonical JSON Profile v1** — a normative subset aligned with what
production *actually needs*, with an **empirical conformance bridge** to npm for anything excluded from the proof.

**Proposed profile rules:**

| Rule | Rationale |
|---|---|
| Objects, arrays, strings, booleans, null | Matches all fixtures |
| Numbers: **either** (A) integers with \|n\| ≤ 2⁵³−1 **or** (B) fixed-point rationals encoded as integers (e.g. micro-units) | Avoids IEEE printing in Lean |
| Strings: UTF-8 valid; document NFC vs code-unit preservation (**match npm: preserve parsed code units, do not normalize**) | `unicode.json` behavior |
| Keys: sorted by **UTF-16 code unit** lexicographic order | RFC 8785; Lean adapter required |
| No `NaN`, `±Infinity`, undefined properties | Already rejected by npm |
| Max depth / size limits | Operational bound (observed depth 8) |

**Critical honesty:** **Current omega-contracts fixtures violate integer-only subset (A).**
Adoption requires **schema + adapter migration**:

- Replace `number` scores 0–1 with **`integer` millibasis** (0–1000) or **`string` decimal** (loses numeric schema)
- Or: keep floats in production JCS; Lean proves integer-only **core envelope** fields; float sub-objects covered by **conformance corpus only** (weaker but shippable)

**Refund demo path:** integer-only migration is easy for demo records; **trust-stack canonical shapes are not integer-only today**.

### 3.3 SPEC.md amendment sketch (not applied — recon only)

Add §7.1 **OMEGA Canonical JSON Profile**:

```markdown
> **OMEGA Profile (normative for content_hash).** Records MUST use JSON values only from:
> objects, arrays, strings, booleans, and null. Numeric fields MUST be integers with
> |n| ≤ 9007199254740991 (2⁵³−1), OR fixed-point scores encoded as integers (e.g.
> score_milli: 760 meaning 0.760). Non-integer JSON numbers are PROHIBITED in
> hashable records. Unicode strings MUST be valid UTF-8; canonicalization preserves
> code unit sequences (no NFC re-encoding). Object keys MUST be sorted by UTF-16 code
> unit value ascending (RFC 8785 §3.2.3).
```

**Migration check against Step 2:** **FAILS** on current `fixtures/*/canonical.expected.json`
without score representation change. **PASSES** on `omega-demo/examples/refund-escalation.json`
numbers (still fails schema alignment — demo fields).

### 3.4 Lean ↔ production string comparison trap

| Layer | Comparison basis |
|---|---|
| RFC 8785 / npm `canonicalize` | UTF-16 **code units** |
| Lean 4 `String` default | Unicode **scalar values** (code points) |
| **Adapter needed** | `utf16CodeUnitCompare : String → String → Ordering` used only for key sort |

Where it matters: supplementary-plane characters (surrogate pairs) and lone surrogates.
`weird.json` proves npm handles emoji keys correctly; Lean must not use default `String.compare` for JCS keys.

---

## Step 4 — Refinement architecture proposal

### 4.1 Lean-side design (new module — **not** shipped in Phase 2 recon)

Recommend new library root `OmegaJCS` (parallel to `OmegaP3Semantic`, promoted when ready):

```lean
/-- OMEGA profile JSON (inductive — avoids Lean.Json number opaque). -/
inductive OmegaJson
  | null
  | bool (b : Bool)
  | int (n : Int)      -- |n| ≤ 2^53-1 enforced by WF predicate
  | str (s : String)
  | arr (xs : List OmegaJson)
  | obj (fields : List (String × OmegaJson))  -- pre-sorted by utf16KeyLt

structure OmegaRecordJCS where
  record_id : String
  schema_version : String
  -- … mirror omega-record.schema.json …
  omitting content_hash signature for hashing

def utf16KeyLt (a b : String) : Bool := …  -- code-unit lex order
def jcsEncode : OmegaJson → String
def jcsDecode : String → Option OmegaJson
def decode_encode : ∀ v, WF v → jcsDecode (jcsEncode v) = some v
def jcsInjective : …  -- from roundtrip on WF values
```

**Lean.Json reuse:** `Lean.Json` stores numbers as `JsonNumber` (opaque decimal string
internally). Fighting it for proofs is awkward; **custom `OmegaJson` inductive** is cleaner for a restricted profile.

### 4.2 Relation to existing `OmegaP3Semantic.Record`

Current model:

```
Record.payload : ByteArray  -- opaque bytes
canonicalBytes := encodeSeqNum ++ encodePrevHash ++ payload
content_hash := compute_hash canonicalBytes
```

**Option (a) — payload carries JCS (recommended):**

- `payload := UTF-8 bytes of jcsEncode omegaRecordJson`
- Chain linkage unchanged (`prev_hash`, `seq_num` framing stays)
- `tamper_implies_collision` / `decode_encode` extend to JCS payload layer
- **Migration cost:** replace `payload` semantics; re-prove injectivity on `OmegaJson` WF not raw bytes; ~**5 theorems** touched (`tamper_implies_collision`, `chain_integrity_extends`, `valid_chain_extend`, `canonicalBytes_injective_wf` → JCS version)

**Option (b) — replace Record entirely:**

- Record fields mirror `OmegaRecord` schema; `canonicalBytes := UTF-8 jcsEncode record`
- Drops binary tuple encoding; **breaks** existing `decodeCanonical` proofs
- **Higher migration cost:** rewrite P3 encoding proofs from scratch

**Recommendation:** **(a)** — minimal disruption to chain structure; JCS is payload interpretation.

### 4.3 Conformance bridge (production link)

Because verified TypeScript → Lean extraction is out of scope:

1. **Generated corpus:** `N` `OmegaRecord` values (adversarial: key order traps, integer edge cases, nested arrays, Unicode strings).
2. **Dual run:** `npm canonicalize` vs `lake exe omega-jcs-encode` (or `#eval` in test module).
3. **Assert:** UTF-8 bytes identical; SHA-256 matches.
4. CI gate in `omega-contracts` + `lean-proof/scratch` (later promoted to `lean-proof/test/`).

This replaces a verified-TS story with **reproducible empirical linkage** — acceptable given npm passes RFC vectors.

### 4.4 Landmines (dependency order + estimates)

| # | Landmine | Effort | Blocks |
|---|---|---|---|
| 1 | UTF-16 code-unit key comparator in Lean | 2–3 days | Correct object key order |
| 2 | String escape table (encode + decode) | 3–4 days | Roundtrip |
| 3 | Integer decimal printing (no float) | 1–2 days | Profile numbers |
| 4 | `OmegaJson` WF predicate + decoder totality on subset | 3–5 days | `decode_encode` |
| 5 | Schema migration float → fixed-point OR corpus-only float policy | 1–2 weeks (cross-repo) | Spec honesty |
| 6 | IEEE-754 float printing (if full JCS required) | **3–6 months** | Production parity with trust scores |
| 7 | `OmegaP3Semantic` payload re-interpretation + theorem replay | 1 week | End-to-end proof |

---

## Step 5 — Phase plan & first PR

### 5.1 Deliverables (this recon)

| Artifact | Path |
|---|---|
| This document | `lean-proof/JCS_RECON.md` |
| Scratch runner | `lean-proof/scratch/jcs-conformance-test.mjs` |
| Machine results | `lean-proof/scratch/jcs-conformance-results.json` |
| Vendored vectors | `lean-proof/scratch/jcs-testdata/` |
| Scratch README | `lean-proof/scratch/README.md` |

### 5.2 Recommended phase sequence

| Phase | Goal | Duration |
|---|---|---|
| **2a** | SPEC §7.1 profile + score integerization decision (milli scores?) | 1 week design |
| **2b** | `OmegaJCS.lean` (new non-shipped module): inductive + integer encode + UTF-16 sort + escape + `decode_encode` | 1–2 weeks |
| **2c** | Conformance corpus generator + CI byte-identity gate vs npm | 3–5 days |
| **2d** | Wire `OmegaP3Semantic.payload` interpretation + replay tamper theorems | 1 week |
| **2e** | Promote `OmegaJCS` to shipped root; update assurance docs | 2–3 days |

### 5.3 First PR-sized chunk (recommended)

**PR 1: "JCS profile foundation (non-shipped)"**

1. Add `lean-proof/OmegaJCS/` (or `lean-proof/JCS/`) — **NOT** in default Lake roots yet
2. Implement: `OmegaJson`, `utf16KeyLt`, `jcsEscape`, `jcsEncodeInt`, property tests in Lean
3. Promote scratch script → `lean-proof/scratch/` CI job comparing Lean `#eval` output to npm on **integer-only** hand-crafted fixtures (10–20 cases)
4. Draft SPEC §7.1 text as `lean-proof/docs/JCS_PROFILE_DRAFT.md` (not SPEC.md itself)
5. **Do not** touch `OmegaP3Semantic.lean` shipped theorems

**Decision gate before PR 2:** choose float policy:

- **A)** Migrate scores to integer milli-units (schema bump, fixture rewrite), or  
- **B)** Lean-proves integer envelope; floats empirically gated by corpus only

---

## Appendix A — Full official vector expected/got strings

```
arrays:     [56,{"1":[],"10":null,"d":true}]
french:     {"peach":"This sorting order","péché":"is wrong according to French","pêche":"but canonicalization MUST","sin":"ignore locale"}
structures: {"":"empty","1":{"\n":56,"f":{"F":5,"f":"hi"}},"10":{},"111":[{"E":"no","e":"yes"}],"A":{},"a":{}}
unicode:    {"Unnormalized Unicode":"Å"}
values:     {"literals":[null,true,false],"numbers":[333333333.3333333,1e+30,4.5,0.002,1e-27],"string":"€$\u000f\nA'B\"\\\\\"/"}
weird:      {"\n":"Newline","\r":"Carriage Return","1":"One","</script>":"Browser Challenge","\u0080":"Control\u007f","ö":"Latin Small Letter O With Diaeresis","€":"Euro Sign","😂":"Smiley","דּ":"Hebrew Letter Dalet With Dagesh"}
```

## Appendix B — Reproduce

```bash
cd lean-proof/scratch
npm install
node jcs-conformance-test.mjs | tee jcs-conformance-results.json
```

---

*End of JCS_RECON.*
