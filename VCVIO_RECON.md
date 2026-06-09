# VCVIO_RECON — VCVio @ v4.27.0 (lean-proof)

**Date:** 2026-06-09  
**Scope:** Read-only inventory of `.lake/packages/VCVio`  
**Pin:** `lake-manifest.json` → `rev: 0dbb0a202445c14219f505d20eb523012f78a31c`, tag `v4.27.0`

---

## 1. Package status

| Field | Value |
|---|---|
| Path | `/Users/warre/Omega/lean-proof/.lake/packages/VCVio` |
| Remote | `https://github.com/dtumad/VCV-io.git` |
| HEAD | `0dbb0a2` (`feat: update to 4.27 (#97)`) |
| Lean toolchain | `leanprover/lean4:v4.27.0` |
| Mathlib (transitive) | `v4.27.0` |

Omega declares VCVio in `lakefile.lean` but **shipped roots do not import it**.

---

## 2. `VCVio.CryptoFoundations` inventory @ v4.27.0

### Active

| Item | File | Statement |
|---|---|---|
| `negligible` | `VCVio/CryptoFoundations/Asymptotics/Negligible.lean` | `def negligible (f : ℕ → ℝ≥0∞) : Prop := SuperpolynomialDecay atTop (λ x ↦ ↑x) f` |
| `negligible_iff` | same | `@[simp] def negligible_iff ... := Iff.rfl` |
| `ProbComp` | `VCVio/OracleComp/ProbComp.lean` | `abbrev ProbComp := OracleComp unifSpec` |
| `OracleComp` | `VCVio/OracleComp/OracleComp.lean` | Free monad over oracle queries |
| `Pr[= x \| comp]`, `Pr[p \| comp]` | `OracleComp/EvalDist.lean` | Output/event probability notation |

### Absent or entirely commented

| Module | Status |
|---|---|
| `CollisionResistance.lean` | **Not in tree** at v4.27.0 |
| `HardnessAssumptions/HardRelation.lean` | All definitions commented |
| `HardnessAssumptions/HardHomogeneousSpace.lean` | All games commented |
| `SecExp.lean` | `SecAdv`, `SecExp`, `advantage` — all commented |
| `Asymptotics/PolyTimeOC.lean` | Entire file commented |
| `Asymptotics/Security.lean` | **Absent** |
| `LibSodium/SHA2.lean` | **0 bytes** (empty stub) |

### Commented hardness-assumption skeleton (design intent)

```lean
-- structure HardRelation ... extends GenerableRelation spec X W r where
--   relation_hard : ∀ (adv : SecAdv spec X W),
--     negligible (hardRelationExp toGenerableRelation adv).advantage
```

File: `VCVio/CryptoFoundations/HardnessAssumptions/HardRelation.lean`

### Commented reduction example (not compiled)

```lean
-- theorem IND_CPA_advantage_eq_parallelTesting_advantage ...
--     (IND_CPA_advantage adversary) =
--       (parallelTestingAdvantage (IND_CPA_parallelTesting_reduction adversary)) := by
--     sorry
```

File: `Examples/HHS_Elgamal.lean`

---

## 3. `LibSodium/SHA2.lean`

| File | Size | Status |
|---|---|---|
| `LibSodium/SHA2.lean` | 0 bytes | Empty stub |
| `LibSodium.lean` | imports SHA2 | Referenced, unimplemented |
| `lakefile.lean` `extern_lib` | commented | FFI not wired |

Omega `compute_hash` remains `opaque` with no VCVio SHA-256 binding.

---

## 4. Restating `tamper_detection` as a VCVio reduction

### Current (deterministic, OmegaP3Semantic)

Given `P3_Traceability chain` and `PayloadTamper chain tampered`, prove `¬ P3_Traceability tampered`.

Reduction inside proof:
1. `compute_hash tamperedRec.canonicalBytes = compute_hash original.canonicalBytes` (from hash conjuncts)
2. `compute_hash_collision_resistant` → byte equality
3. `canonicalBytes_injective_wf` (theorem, WF records) → payload equality → contradicts tamper

### Target (computational)

```lean
theorem tamper_detection_computational :
  ∀ (A : ∀ λ, PayloadTamperAdversary (chain λ)), PolyTimeAdversary A →
    negligible (fun λ => tamper_advantage λ A)
```

**Game:** PPT adversary outputs `(chain', tampered')` with both chains P3-valid and payload tampered.

**Reduction:** On tamper success, return collision pair
`(tamperedRec.canonicalBytes, original.canonicalBytes)` against keyed hash family `H λ`.

**What replaces the axiom:**

```lean
axiom sha256_collision_resistant :
  ∀ (A : ∀ λ, KeyedCRAdversary (Key λ) ByteArray),
    PolyTimeAdversary A → negligible (λ ↦ keyedCRAdvantage (H λ) (A λ))
```

### Type mapping

| Omega (today) | VCVio replacement |
|---|---|
| `structure Record` | `Record λ` with `content_hash : Hash λ` |
| `compute_hash : ByteArray → ByteArray` | `H.hash (k : Key λ) : ByteArray → Hash λ` |
| `compute_hash_collision_resistant` (injectivity axiom) | `negligible (keyedCRAdvantage ...)` |
| `P3_Traceability` | Same predicate, λ-indexed, threads `H.hash` |
| `canonicalBytes_injective_wf` | **Stays a theorem** (encoding layer) |

---

## 5. Blockers

| Blocker | Impact |
|---|---|
| No `CollisionResistance.lean` at v4.27.0 | Cannot state keyed CR games in-tree |
| `SecExp` / `SecAdv` commented | No standard security-experiment API |
| `PolyTimeOC` commented | No `PolyTimeAdversary` class |
| `LibSodium/SHA2.lean` empty | No verified SHA-256 term |
| Mathlib import boundary | First VCVio import pulls large transitive closure; shipped modules ban `import Mathlib` |
| λ-indexing refactor | Omega `Record`/`List Record` are non-indexed; games are `ℕ → Type` |
| `ByteArray` vs oracle model | Need bridge layer between deterministic Prop predicates and `ProbComp` games |

### Minimum unblock sequence

1. Vendor or uncomment `SecExp` + `SecAdv` + `advantage`
2. Add `CollisionResistance.lean` (from `main` or hand-rolled)
3. Define `KeyedHashFamily` + computational CR axiom
4. λ-index `Record` / `P3_Traceability`
5. Prove reduction reusing existing `tamper_detection` skeleton
6. Populate SHA2 later (optional for correct *statement* of CR)

---

## 6. Summary

| Capability | v4.27.0 |
|---|---|
| `OracleComp` / `ProbComp` / probability notation | Ready |
| `negligible` | Active (3 lemmas) |
| Security games / adversaries | Commented skeleton only |
| Collision resistance definitions | Not present |
| PPT adversaries | Not present |
| SHA-256 FFI | 0-byte stub |
| Compiled reduction example | None |
| Omega `tamper_detection` → VCVio | Conceptually 2 rewrites; infrastructure missing |

---

## 5. VCVio dependency removed (2026-06-09, PIN2)

**Rationale:** The constructive tamper-evidence theorem `tamper_implies_collision`
supersedes the former `compute_hash_collision_resistant` user axiom. VCVio was
declared in `lakefile.lean` but never imported by shipped roots; at v4.27.0 its
security-game API (`SecExp`, `SecAdv`, collision-resistance games) is commented
out upstream and `LibSodium/SHA2.lean` remains empty. Keeping VCVio pulled Mathlib
(~32 s cold build) with no proof benefit.

**Actions:**
- Removed `require VCVio` from `lakefile.lean`; `lake-manifest.json` packages list is empty.
- Deleted `probes/VCVioProbe.lean` (imported VCVio; would fail without the dependency).
- Cold build without VCVio: ~1.4 s (was ~32 s with transitive Mathlib).

A future VCVio migration remains tracked in `VCVIO_MIGRATION.md` for when upstream
ships the security-game API and SHA-256 FFI slot.
