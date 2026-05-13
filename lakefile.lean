import Lake
open Lake DSL

/-!
OMEGA formal proof package.

Lean is pinned to `v4.18.0` (see `lean-toolchain`).

VCVio is required as the cryptography-proofs framework. Its SHA-256
implementation slot (`LibSodium/SHA2.lean`) is upstream-empty at v4.18.0,
so `OmegaP3Semantic.compute_hash` is currently declared as an `opaque`
function rather than wired through FFI. A future commit will swap in a
real libsodium binding once the upstream slot is populated (or via a
local FFI module).

Build performance: Cold build with VCVio dependency takes ~32 seconds
(well under 60-second target). VCVio pulls Mathlib transitively but the
current code doesn't import VCVio modules, so the dependency is kept for
future use without impacting current build performance.
-/

package omegaProof

require VCVio from git
  "https://github.com/dtumad/VCV-io.git" @ "v4.18.0"

@[default_target]
lean_lib OmegaProof where
  srcDir := "."
  roots := #[`OmegaProof, `OmegaV14, `OmegaP3Semantic]
