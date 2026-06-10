# lean-proof

## PURPOSE
Public Lean 4 Lake package formalising the OMEGA `Governed` predicate
(v1.3 17-conjunct, v1.4.1 22-conjunct), the `P3_Traceability` concrete hash
chain, `P1_Governance`, the `FailureProtocol` escalation rule, an append-only
`OmegaHashChain`, and an `OmegaGovernance` decision-gravity partial order.
This is **doctrine-layer scaffolding** — Lean proves statements about
*definitions*, not that production systems satisfy them (see
`docs/ASSURANCE_BOUNDARY.md` and `failure-protocol.md`).

## STATUS
Live. Toolchain pinned `leanprover/lean4:v4.27.0`. All **eight** shipped Lake
roots build cleanly with **zero `sorry`** in shipped modules (the eighth,
`OmegaJCSChain`, is the chain↔JCS bridge over the conformance-tested
`OmegaJCS` encoder; promoted PIN3, 2026-06-10). SafeVerify (@ Lean v4.27.0)
replay **pass** on `OmegaProof`/`OmegaV14`/`OmegaP3Semantic`/`OmegaJCSChain`
as of 2026-06-10. `OmegaV15.lean` (parallel 29-conjunct doctrine) is **not**
in Lake roots and still has one open `sorry`. HEAD `61d3c9d` ("feat(jcs):
chain-JCS bridge … OmegaJCS promoted to attested roots (eight)").

## STACK
- Lean 4 v4.27.0 (`lean-toolchain` pinned).
- Lake build system (`lakefile.lean`).
- `VCVio` from `https://github.com/dtumad/VCV-io.git` @ tag `v4.27.0` —
  required as crypto-proofs framework; pulls Mathlib transitively but the
  shipped modules do **not** import VCVio (kept for future SHA-256 wiring).
- External verifier: SafeVerify `main` @ Lean v4.27.0 (cached under
  `.cache/SafeVerify`).

## ENTRY POINTS
- `lakefile.lean` — package `omegaProof`, default target `OmegaProof` library.
  Roots: `OmegaProof, OmegaV14, OmegaP3Semantic, OmegaP1Governance,
  FailureProtocol, OmegaHashChain, OmegaGovernance`.
- `OmegaProof.lean` (v1.3, 17-conjunct, 37 theorems).
- `OmegaV14.lean` (v1.4.1, 22-conjunct, 13 theorems).
- `OmegaP3Semantic.lean` — concrete hash-chain predicate, real
  tamper-detection proof.
- `OmegaP1Governance.lean` — contract+agent presence predicate.
- `FailureProtocol.lean` + `failure-protocol.md` — six-case `FailureAction`
  inductive; one theorem (`retries_exceed_limit_implies_escalation`).
- `OmegaHashChain.lean`, `OmegaGovernance.lean` — append-only chain lemmas
  and G1–G4 decision-gravity partial order.
- `OmegaV15.lean` — parallel v1.5 work-in-progress, not in Lake roots.
- `probes/AxiomProbe.lean`, `probes/VCVioProbe.lean` — reproducibility probes.
- `v12-source/omega_v12_lean4_proof.lean` — byte-identical legacy v1.2 copy
  for provenance; **not** built by Lake.
- `VCVIO_MIGRATION.md` — migration assessment for the SHA-256 swap.

## CONVENTIONS
- Shipped modules use only `Prop`, `∧`, `¬`, `fun`, `Iff` (except
  `OmegaP3Semantic` which has two named declarations: `compute_hash`
  opaque and the single axiom `compute_hash_collision_resistant`; the
  former `canonicalBytes_injective` axiom was false and is now the proven
  theorem `canonicalBytes_injective_wf` on WF records).
- No `import Mathlib` in shipped modules; Mathlib only enters transitively
  via VCVio at the lake level.
- `#print axioms` receipts recorded in `README.md` — update when adding any
  axiom-bearing theorem.
- `sorry` is banned in Lake roots. WIP versions (e.g. `OmegaV15`) live
  outside the root list until clean.
- Tests/probes are `.lean` files invoked via `lake env lean <file>`.

## DEPENDENCIES
- External: VCVio @ v4.27.0 (lake `require`), Mathlib (transitive via
  VCVio), SafeVerify @ v4.27.0 (external verifier, cached locally).
- Toolchain: `leanprover/lean4:v4.27.0` only — pinned for SafeVerify
  compatibility; do not bump without rerunning the SafeVerify pipeline.
- Internal: implementation-status map at
  `omega-contracts/docs/PRIMITIVE_MAP.md` (Lean = conceptual/doctrine layer).

## GOTCHAS
- **Toolchain is pinned.** Do not bump past v4.27.0 — lean4lean @ v4.29.0
  segfaults / hits kernel deep-recursion on `OmegaProof`, and SafeVerify is
  pinned to v4.27.0. Bumping breaks attestation.
- VCVio's `LibSodium/SHA2.lean` slot is **upstream-empty** at v4.27.0 —
  `OmegaP3Semantic.compute_hash` is declared `opaque` until the slot is
  populated (see `VCVIO_MIGRATION.md` and the "Next step" section of
  README.md).
- `compute_hash_collision_resistant` is the SOLE user-declared axiom in
  shipped modules; it lives in `OmegaP3Semantic.lean` and enters only
  `tamper_detection`. The former second axiom `canonicalBytes_injective`
  was removed 2026-06-09 (it was false in the model — see the
  machine-checked `old_axiom_was_false` theorems and the
  `docs/ASSURANCE_BOUNDARY.md` changelog).
- Cold build with VCVio is ~32 s (well under 60 s target). Pulling Mathlib
  transitively can blow `.lake/` to several GB.
- `OmegaV15.lean` is intentionally not a Lake root — do not add it without
  closing its `sorry`.
- Lean is a doctrine layer — do not claim Lean proofs cover runtime
  behaviour. See `docs/ASSURANCE_BOUNDARY.md` before writing assurance
  claims.

## Session rules
1. **Account for the working tree at session start.** Run `git status` and
   explain every modification and untracked file against a known author/task.
   If any change has no known author, STOP and ask before building on top of it.
2. **Do not add Lake roots or touch `lakefile.lean` outside an explicitly
   scoped task.** A new attested root changes the public surface; it needs its
   own review. (This rule was added after `OmegaP5Gate` appeared on `main`'s
   roots from an unscoped parallel session; it now lives on branch `wip/p5gate`.)
3. **`lake build` from a clean tree before claiming any gate.** "It builds" and
   "the gate passes" are only true after a from-clean build, not an incremental one.

## LAST UPDATED
2026-06-10 (session-hygiene rules added; OmegaP5Gate moved off main to wip/p5gate)
