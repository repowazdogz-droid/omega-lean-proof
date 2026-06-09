import Lake
open Lake DSL

/-!
OMEGA formal proof package.

Lean is pinned to `v4.27.0` (see `lean-toolchain`).

No external Lake dependencies — shipped roots are self-contained.
VCVio was removed 2026-06-09 (security-game API commented out upstream
at v4.27.0; see VCVIO_RECON.md). `compute_hash` remains `opaque`.
-/

package omegaProof

@[default_target]
lean_lib OmegaProof where
  srcDir := "."
  roots := #[`OmegaProof, `OmegaV14, `OmegaP3Semantic, `OmegaP1Governance, `FailureProtocol, `OmegaHashChain, `OmegaGovernance]
