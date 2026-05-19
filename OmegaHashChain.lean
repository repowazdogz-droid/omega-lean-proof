-- OMEGA hash chain — append-only structural lemmas
-- Goal contract reference: /Users/warre/Omega/unified-forge/goal-contract.md
-- Verification: `lake build` from /Users/warre/Omega/lean-proof

import OmegaP3Semantic

namespace OmegaHashChain

open OmegaP3Semantic

/-- Alias for the semantic record used in the hash chain. -/
abbrev OmegaRecord := Record

/-- A chain is valid when it satisfies P3 traceability. -/
def valid_chain (chain : List OmegaRecord) : Prop :=
  P3_Traceability chain

/-- Adding a well-formed record at the tip preserves prior entries unchanged. -/
theorem omega_chain_append_only
    (chain : List OmegaRecord) (r : OmegaRecord) :
    valid_chain chain →
    valid_chain (chain ++ [r]) →
    ∀ (i : Nat) (hi : i < chain.length), chain[i]'hi = (chain ++ [r])[i]'(by
      simpa [List.length_append] using Nat.lt_succ_of_lt hi) := by
  intro _ _ i hi
  rw [List.getElem_append_left hi]

/-- Extending a valid chain by one conformant record yields a valid chain. -/
theorem valid_chain_extend
    (chain : List OmegaRecord) (r : OmegaRecord) :
    valid_chain chain →
    r.content_hash = compute_hash r.canonicalBytes →
    r.prev_hash = next_prev_hash chain →
    r.seq_num = chain.length →
    valid_chain (chain ++ [r]) :=
  chain_integrity_extends chain r

end OmegaHashChain
