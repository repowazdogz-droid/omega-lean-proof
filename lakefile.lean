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
-/

package omegaProof where
  -- Build options for faster compilation
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,  -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- VCVio is required for future cryptographic proofs but not currently used
-- We keep it as a dependency but don't build its heavy Mathlib dependency
require VCVio from git
  "https://github.com/dtumad/VCV-io.git" @ "v4.18.0"

@[default_target]
lean_lib OmegaProof where
  srcDir := "."
  roots := #[`OmegaProof, `OmegaV14, `OmegaP3Semantic]
