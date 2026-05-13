import Lake
open Lake DSL

/-!
OMEGA formal proof package.

Lean is pinned to `v4.18.0` (see `lean-toolchain`). VCVio is required so
`OmegaP3Semantic` can eventually replace its `compute_hash` axiom with a
verified SHA-256 implementation.
-/

package omegaProof

require VCVio from git
  "https://github.com/dtumad/VCV-io.git" @ "v4.18.0"

@[default_target]
lean_lib OmegaProof where
  srcDir := "."
  roots := #[`OmegaProof, `OmegaV14, `OmegaP3Semantic]
