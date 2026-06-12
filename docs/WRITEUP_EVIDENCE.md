# WRITEUP_EVIDENCE — receipts for the v1.5 writeup

Every claim in the blog draft (`omega-site-deploy/public/notes/false-axiom/`)
and the companion shorts cites an anchor in this file. All code is quoted
**byte-for-byte from the tree at PIN3 (`61d3c9d`)** unless an explicit earlier
ref is given. Repo: <https://github.com/repowazdogz-droid/omega-lean-proof>.

Pins:
- **PIN1** = `4957d4b` (2026-06-09) — `canonicalBytes_injective` refuted and replaced.
- **PIN2** = `b5070b8` (2026-06-09) — zero user-declared axioms.
- **PIN3** = `61d3c9d` (2026-06-10) — `OmegaJCSChain` promoted; eight attested roots.

---

## [E1] Timeline (git log, `omega-lean-proof`)

| ref | date | what |
|---|---|---|
| `1a6afa2` | 2026-05-13 | OmegaV14 — 22nd conjunct `P_ChainIntegrity` added (the chain-integrity primitive). |
| `d395f40` | 2026-05-13 | OmegaP3Semantic — P3 Traceability stated as a concrete hash-chain predicate (3 theorems, `sorry`). |
| `17fc3f1` | 2026-05-13 | P3 semantic extension — `tamper_detection` "proven", `compute_hash_injective` axiom introduced, contiguity added. |
| **`93db6cd`** | **2026-05-13** | **Original axiom landing** — "fold seq_num into canonicalBytes"; this commit adds `axiom canonicalBytes_injective` (see [E2]). |
| `bdc89d0` | 2026-05-13 | "fold prev_hash into canonicalBytes — closes prev_hash rewrite attack vector". |
| (event) | 2026-05-13 | **DeepSeek adversarial review.** Cited in-tree at `OmegaP3Semantic.lean:9` — *"Adversarial review applied 2026-05-13 (DeepSeek). Three gaps closed"* — and `:385`. It reviewed `OmegaP3Semantic.lean`, closed three gaps (seq_num, prev_hash, contiguity), and **missed** that `canonicalBytes_injective` asserts a falsehood. This review was an AI-assisted session (see [E9]). |
| **`4957d4b`** | **2026-06-09 (PIN1)** | "canonicalBytes_injective axiom was false (truncation + framing ambiguity); replaced by proven injectivity on WF records; WF threaded through P3_Traceability". |
| **`b5070b8`** | **2026-06-09 (PIN2)** | "zero user axioms — tamper-evidence restated as constructive collision extraction; VCVio dependency removed". |
| `d341f9b` | 2026-06-09 | OmegaJCS encoder/decoder foundation (non-shipped); npm corpus green. |
| `cd355c3` | 2026-06-09 | `parseStringChars` made a well-founded `def` (drop `partial`) so it reduces. |
| `224fa88` | 2026-06-10 | **JCS bug (a) fix** — number-parse roundtrip sound: `NoLeadDigit` precondition (see [E7]). |
| `0888a18` | 2026-06-10 | EncodeList green — `nodeCount` fuel bound (the bound later found off-by-one; see [E7b]). |
| `606d912` | 2026-06-10 | **JCS bug (b) fix** — roundtrip + injectivity closed; `nodeCount` bound replaced by strong induction on encoded **length** (see [E7b]). Zero `sorry` in OmegaJCS. |
| **`61d3c9d`** | **2026-06-10 (PIN3)** | "chain-JCS bridge — JSON-level tamper provably forces SHA-256 collision; OmegaJCS promoted to attested roots (eight)". |
| `4bb2db5` | 2026-06-10 | docs: ASSURANCE_BOUNDARY + CLAUDE reflect PIN3 eight roots; gap closed at payload level. |

---

## [E2] The original axiom, as it shipped

From `git show 4957d4b^:OmegaP3Semantic.lean` (i.e. the last tree before PIN1
removed it; introduced at `93db6cd`):

```lean
axiom canonicalBytes_injective :
  ∀ r1 r2 : Record,
    r1.canonicalBytes = r2.canonicalBytes →
    r1.seq_num = r2.seq_num ∧ r1.prev_hash = r2.prev_hash ∧ r1.payload = r2.payload
```

`canonicalBytes` is a **defined** Lean function over `Record`, so this axiom
asserts a property of code, not of an abstract primitive.

## [E3] The two refutations, as they now exist in tree (PIN3)

`OmegaP3Semantic.lean` (each closes with a concrete witness `by` proof in tree):

```lean
theorem old_axiom_was_false :
    ∃ r1 r2 : Record, r1.canonicalBytes = r2.canonicalBytes ∧
      r1.payload ≠ r2.payload := by
  ...
```

```lean
theorem old_axiom_was_false_seqnum :
    ∃ r1 r2 : Record, r1.canonicalBytes = r2.canonicalBytes ∧
      r1.seq_num ≠ r2.seq_num := by
  ...
```

The two failure mechanisms: **(a) framing ambiguity** — `encodePrevHash (some bs)
= 0x01 ++ bs` carries no length delimiter, so bytes migrate between `prev_hash`
and `payload`; **(b) 64-bit truncation** — `seq_num : Nat` is unbounded but the
encoder keeps only the low 64 bits, so `seq_num = 0` and `seq_num = 2^64` encode
identically. Both are dated 2026-05-13 in the source comments and fixed at PIN1.

## [E4] The constructive replacement: `tamper_implies_collision` (PIN3)

```lean
theorem tamper_implies_collision (chain tampered : List Record) :
    P3_Traceability chain →
    PayloadTamper chain tampered →
    P3_Traceability tampered →
    ∃ a b : ByteArray, a ≠ b ∧ compute_hash a = compute_hash b := by
  ...
```

No injectivity or collision-resistance axiom; the proof extracts an explicit
colliding pair `(original.canonicalBytes, tamperedRec.canonicalBytes)` using the
proven `canonicalBytes_injective_wf` (injectivity on `Record.WF` records).

## [E5] The four JCS theorems (PIN3, `OmegaJCS/Roundtrip.lean`)

```lean
theorem parse_encode (v : OmegaJson) (h : v.WF) (fuel : Nat) (rest : List Char)
    (hrest : NoLeadDigit rest) (hfuel : (jcsEncodeChars v).length < fuel) :
    parseValueFuel fuel (jcsEncodeChars v ++ rest) = some (v, rest)

theorem decode_encode (v : OmegaJson) (h : v.WF) :
    jcsDecode (jcsEncode v) = some v

theorem jcsEncode_injective (v w : OmegaJson) (hv : v.WF) (hw : w.WF)
    (h : jcsEncode v = jcsEncode w) : v = w

theorem canonicalBytesJCS_injective (v w : OmegaJson) (hv : v.WF) (hw : w.WF)
    (h : canonicalBytesJCS v = canonicalBytesJCS w) : v = w
```

## [E6] The bridge theorem (PIN3, `OmegaJCSChain.lean`)

```lean
theorem json_tamper_implies_collision
    (chain tampered : List Record) (v v' : OmegaJson) :
    P3_Traceability chain →
    JsonTamper chain tampered v v' →
    P3_Traceability tampered →
    ∃ a b : ByteArray, a ≠ b ∧ compute_hash a = compute_hash b
```
with `jsonPayload v := canonicalBytesJCS v` and `Record.payload = jsonPayload v`.

---

## [E7] JCS bug (a): number-parse follow-set precondition

Commit `224fa88` (2026-06-10). An intermediate lemma asserted
`parseInt (intToStringChars n ++ rest) = some (n, rest)` for an **arbitrary**
continuation `rest`. False — the greedy digit parser consumes following digits.
Verified counterexample (from the commit message and reproduced at PIN3):

```
parseInt (intToStringChars 12 ++ ['5']) = some (125, [])     -- not some (12, ['5'])
```

Fix: a `NoLeadDigit rest` precondition (the continuation must not start with a
digit), discharged at every call site because a number's continuation in a JSON
value is always a structural byte (`,` `]` `}` `:`) or end-of-input.

## [E7b] JCS bug (b): forward-reference / off-by-one fuel bound

The mutual-recursion roundtrip first used `nodeCount` as the recursion/fuel
measure (`0888a18`). That bound is **off by one** for nested arrays/objects: the
parser decrements fuel once per *structural step*, not once per node (e.g.
`arr [int]` needs fuel 3, not 2). The roundtrip was reformulated by strong
induction on the encoded **length** (`606d912`), eliminating both the unsound
bound and a mutual-recursion forward reference. The kernel rejected every
intermediate form until the measure was correct.

Both [E7] and [E7b] are the **same failure mode as [E2]**: a statement about
defined functions that looked right and was false; the difference is that during
JCS formalization the kernel refused to close them, so they never shipped.

---

## [E8] Receipts at PIN3

**`#print axioms`** (run via the reproduce script [E10]; verbatim output):

```
'p1_necessary' does not depend on any axioms
'OmegaV14.p2_dag_necessary' does not depend on any axioms
'OmegaP3Semantic.tamper_implies_collision' depends on axioms: [propext, Classical.choice, Quot.sound]
'OmegaJCSChain.json_tamper_implies_collision' depends on axioms: [propext, Classical.choice, Quot.sound]
'OmegaJCS.parse_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
'OmegaJCS.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
'OmegaJCS.jcsEncode_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'OmegaJCS.canonicalBytesJCS_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**SafeVerify v1.5 attestation** (excerpt; full file
`public/omega/formal-proof/safeverify-v15-attestation.txt`, also live at
<https://omegaprotocol.org/omega/formal-proof/safeverify-v15-attestation.txt>):

```
SafeVerify replay attestation — OMEGA Protocol v1.5 (eight attested roots)
Date (UTC): 2026-06-10T09:51:40Z
Tool: SafeVerify main @ leanprover/lean4:v4.27.0
Allowlist: propext, Quot.sound, Classical.choice (standard built-ins only)
### OmegaProof.olean    ... Found 38 declarations ... SafeVerify check passed.
### OmegaV14.olean      ... Found 14 declarations ... SafeVerify check passed.
### OmegaP3Semantic.olean ... Found 94 declarations ... SafeVerify check passed.
### OmegaJCSChain.olean ... Found 6 declarations ... SafeVerify check passed.
```

**Encoder conformance corpus** (`lake build jcsDump && node scratch/jcs-corpus-conformance.mjs`):

```
"corpusPassCount": 16, "corpusFailCount": 0,
"refundContentHash":  "e747c3fdcb2966c6f0fafa4ab3b51274e53c70f1bf44c51c662ff26749996c09",
"refundHashMatch": true
```
The corpus compares the Lean encoder byte-for-byte against the production
`canonicalize@3.0.0` path; case `refund-escalation-stripped.json` is the
published refund record, whose content hash reproduces exactly.

## [E9] AI-assistance disclosure (from public git history)

The Lean development was AI-assisted (Cursor agents) throughout, including both
the 2026-05-13 session that introduced the axiom **and** the 2026-06-09 session
that found it false. Verifiable: the refutation/fix commit `4957d4b` shows
`Co-authored-by: Cursor <cursoragent@cursor.com>`; the JCS proof commits ([E1],
2026-06-10) carry a `Co-Authored-By:` trailer naming the assisting model. So the
reviewer that missed the inconsistency and the reviewer that caught it were both
language-model sessions — stated plainly in the post, not framed as a human audit.

## [E10] Reproduce block — TESTED VERBATIM (2026-06-10) in a scratch clone

The following was run end-to-end in `/tmp/reproduce-test` (a fresh clone of the
repo, checkout PIN3, clean build) and produced [E8]'s `#print axioms` output:

```sh
git clone https://github.com/repowazdogz-droid/omega-lean-proof
cd omega-lean-proof
git checkout 61d3c9d
lake build                              # 14 jobs, eight roots, zero sorry
cat > /tmp/axioms.lean <<'EOF'
import OmegaProof
import OmegaV14
import OmegaP3Semantic
import OmegaP1Governance
import FailureProtocol
import OmegaJCSChain
#print axioms p1_necessary
#print axioms OmegaV14.p2_dag_necessary
#print axioms OmegaP3Semantic.tamper_implies_collision
#print axioms OmegaJCSChain.json_tamper_implies_collision
#print axioms OmegaJCS.parse_encode
#print axioms OmegaJCS.decode_encode
#print axioms OmegaJCS.jcsEncode_injective
#print axioms OmegaJCS.canonicalBytesJCS_injective
EOF
lake env lean /tmp/axioms.lean
```
Notes: the encoder-conformance step additionally needs `npm install` (it shells
out to `canonicalize@3.0.0`). SafeVerify replay needs SafeVerify built under
`.cache/SafeVerify/` (gitignored; pinned to Lean v4.27.0) — its verbatim output
is the attestation file in [E8].

---

## [E11] Proof-integrity loop — per-theorem axiom allowlist + sealed replaying report

*Appended 2026-06-13.* The loop at `~/Omega/proof-integrity-loop/` runs
`#print axioms` for every watched theorem and checks that the observed axiom set
is a subset of that theorem's declared allowlist in
`proof_integrity.config.json`; any new axiom, `sorryAx`, `native_decide`, or
renamed/missing theorem fails the run. It writes
`proof_integrity_report.{json,md}` and a LOCAL seal
(`proof_integrity_report.seal.json`). Latest run against merged `lean-proof`
`main`: **OVERALL PASS**, seal id **`LOCAL-20260612-213517-78A768`**; the report
SHA-256 recorded in the seal recomputes to the same value (the report replays).
The sixteen theorems added since the writeup was drafted are watched here: ten
for the P5 decision gate (`OmegaP5Gate.*` — 8×`[propext]`, 2×`[propext,
Quot.sound]`) and six for generation provenance (`OmegaProvenance.*` —
4×`[propext]`, 2×`[]`), each observed at its allowlist.

## [E12] The decision gate's no-false-COMMIT theorem, and the composition-fixture reconciliation

*Appended 2026-06-13.* **Gate.** The deterministic P5 gate (`OmegaP5Gate.lean`,
R1–R22) landed on `lean-proof` `main` at `36bd522` and is current at `c30c583`.
It includes `no_false_commit` — a record any firing rule rejects can never carry
`gate_result = COMMITTED` — kernel-verified with no user axioms (axiom set
`[propext]`; see [E11]). **Fixture.** The `@omega-protocol/contracts` composition
test vector recorded `outcome.gate_result: COMMITTED` while its ethics slot
carried `requires_human_review = 1`, which the shipped evaluator resolves to
ESCALATED (rule R2). It was reconciled in public at commit **`7b3eb31`**: outcome
→ `ESCALATED` / `acted: false`, content hash
**`152eab926412e397…c3d2c705` → `ad7bfe01539227…5925dcf0`**, and the
gate-evaluator "known counterexample" test flipped to assert consistency. A
different artifact from the writeup's Lean axiom; the same rule — when the proofs
and the claims disagree, the claims move.
