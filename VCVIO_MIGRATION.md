# VCVio migration — feasibility assessment

Date: 2026-05-13
Status: assessment only, not yet started

> [Updated 2026-06-07] This assessment was written when the package pinned Lean
> and the VCVio dependency at v4.18.0. Since then the `lean-toolchain` and the
> `lakefile.lean` VCVio `require` were both bumped to **v4.27.0** (2026-05-19).
> References below to "current v4.18.0 pin" are therefore historical; read them
> as v4.27.0 for the present state. The forward migration target for verified
> SHA-256 collision resistance is still a newer VCVio (v4.29.0+ / `main`), so
> the substance of the plan stands; only the starting pin has moved.

## Goal

Replace the current idealised axiom in `OmegaP3Semantic.lean`:

```lean
axiom compute_hash_collision_resistant :
  ∀ a b : ByteArray, compute_hash a = compute_hash b → a = b
```

with a computational security statement using VCVio's oracle model: `tamper_detection` holds against any probabilistic polynomial-time adversary who cannot find SHA-256 collisions with non-negligible probability.

The current axiom is strictly stronger than what SHA-256 actually provides (true injectivity is impossible by pigeonhole). The replacement states the standard cryptographic assumption correctly.

## 1. Does VCVio have the primitives needed?

**Partially.** Pinned tag v4.18.0 has roughly half of what's required; the rest is on `main` or in a newer tag.

Verified by direct fetch of raw files at each ref:

| Primitive | v4.18.0 | v4.29.0 | main |
|---|---|---|---|
| `OracleComp` + program logic | yes | yes | yes |
| `negligible` predicate (`Asymptotics/Negligible.lean`) | yes | yes | yes |
| `SecExp` + `advantage` (`SecExp.lean`) | yes | yes | yes |
| `Asymptotics/Security.lean` (asymptotic wrapper) | 404 | yes | yes |
| `HardnessAssumptions/CollisionResistance.lean` (keyed CR game) | no | no | yes |
| `LibSodium/SHA2.lean` (FFI slot) | **0 bytes** | **0 bytes** | **0 bytes** |

Notes:
- The lakefile docstring's "SHA-256 slot is upstream-empty at v4.18.0" is misleading — the slot is empty on tip, not version-specific.
- The CR game on `main` provides `KeyedCRAdversary` / `keyedCRExp` / `keyedCRAdvantage` but stops at concrete advantage; the caller composes `negligible (fun λ ↦ …)`.
- `HashCommitment.lean` (in VCVio examples) is the closest template to copy: it reduces commitment binding to keyed CR.

**CatCrypt (eprint 2026/604):** the abstract describes a Rust-to-Lean pipeline of 172 protocols built in two months. The PDF was 403-walled to automated fetch; no confirmation that it interoperates with VCVio or provides SHA-256 CR machinery. Treat as "probably not the right tool here" until the PDF is read manually.

## 2. New theorem statement (sketch)

```lean
variable (H : ∀ λ : ℕ, KeyedHashFamily (Key λ) ByteArray (Hash λ))

def tamper_advantage
    (A : ∀ λ, KeyedCRAdversary (Key λ) ByteArray) : ℕ → ℝ≥0∞ :=
  fun λ => keyedCRAdvantage (H λ) (A λ)

axiom sha256_collision_resistant :
  ∀ (A : ∀ λ, KeyedCRAdversary (Key λ) ByteArray),
    PolyTimeAdversary A → negligible (tamper_advantage H A)

theorem tamper_detection
    (chain : ∀ λ, List (Record λ))
    (A : ∀ λ, PayloadTamperAdversary (chain λ)) :
    PolyTimeAdversary A →
    negligible (fun λ => Pr[ P3_Traceability (tamperResult (A λ)) | runAdv (A λ) ])
```

Proof obligation: a reduction. Any PPT adversary producing a P3-valid tampered chain yields a CR-breaker against `H λ`.

Two structural changes:
- `Record` and `canonicalBytes` become λ-indexed (hash output type widens with security parameter).
- `compute_hash : ByteArray → ByteArray` becomes `H.hash : Key λ → ByteArray → Hash λ`.

What survives intact:
- `canonicalBytes_injective` (it's about the encoding, not the hash).
- `chain_integrity_extends` and `chain_no_gaps` (deterministic).

What changes shape:
- `tamper_detection` only — conclusion goes from `¬ P3_Traceability tampered` to `negligible (advantage …)`.

## 3. Lakefile changes required

- **Bump VCVio pin** from `v4.18.0` to `v4.29.0` (first tag with `Asymptotics/Security.lean`). For `CollisionResistance.lean` you must either pin to a `main` commit SHA or vendor the file — no tagged release ships it yet.
- **Bump `lean-toolchain`** from `leanprover/lean4:v4.18.0` to `v4.29.0` (eleven minor versions; this is the part most likely to bite — Mathlib API drift).
- **Do NOT** add a direct `require Mathlib` — VCVio pulls it transitively; duplicate require will conflict.
- New imports in `OmegaP3Semantic.lean`:
  - `VCVio.CryptoFoundations.HardnessAssumptions.CollisionResistance`
  - `VCVio.CryptoFoundations.Asymptotics.Security`
  - `OracleComp.ProbComp`
- `compute_hash` stays opaque/axiomatic (no FFI), replaced by an opaque `KeyedHashFamily` whose security is the new computational axiom. The result remains "modulo the SHA-256 assumption" — but the assumption is now stated correctly.

## 4. Tractability: 2–4 focused weeks

Estimate breakdown:
- ~3 days: toolchain + VCVio bump, shake out Mathlib API drift across 11 minor versions (usually the most painful part).
- ~3 days: introduce λ-indexing through `Record` and the chain predicates.
- ~1 week: write the reduction proof (PayloadTamper-breaker → keyed-CR-breaker) and glue.
- ~3 days slack for proof-engineering surprises.

Where the current proof applies `compute_hash_collision_resistant` to contradict the tamper hypothesis, the new proof packages the same equality as a returned collision pair `(tamperedRec.canonicalBytes, original.canonicalBytes)`. The reduction is two structural rewrites away from the current proof.

**Hard blocker only if** the user insists the SHA-256 *implementation* be verified rather than axiomatised — that requires LibSodium's empty slot filled upstream, or a from-scratch Lean SHA-256 (multi-month). For the stated goal — "axiom is computational, not idealised-injective" — implementation is not required.

**Recommendation:** worth doing. Status improvement is real (false injectivity claim → standard cryptographic assumption stated as a computational reduction), the math is well-trodden, and the existing `HashCommitment.lean` pattern in VCVio is essentially the same shape. Main risk is the Mathlib bump, not the cryptography.

## Sources

- `https://github.com/dtumad/VCV-io` (tree, tags, raw files at v4.18.0, v4.29.0, main)
- `https://github.com/Verified-zkEVM/VCV-io` (distinct organisation mirror; same Devon Tuma framework, different maintenance org)
- `https://eprint.iacr.org/2026/604` (CatCrypt abstract page; PDF inaccessible to automated fetch)
- `https://eprint.iacr.org/2026/899` (VCVio companion paper by Devon Tuma; PDF inaccessible)
- `/Users/warre/Omega/lean-proof/OmegaP3Semantic.lean` (current axiom + `tamper_detection` proof)
- `/Users/warre/Omega/lean-proof/lakefile.lean` (current v4.18.0 pin)
