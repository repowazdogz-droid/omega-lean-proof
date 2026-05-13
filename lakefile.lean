import Lake
open Lake DSL

/-!
OMEGA formal proof package (no Mathlib dependency).

Lean is pinned to `v4.15.0` so `.olean` files are compatible with the
`SafeVerify` branch `minif2f-kimina-check` (Lean 4.15.0). Mathlib `v4.15.0`
uses the same toolchain if you later add Mathlib as a dependency.
-/

package omegaProof

@[default_target]
lean_lib OmegaProof where
  srcDir := "."
  roots := #[`OmegaProof, `OmegaV14]
