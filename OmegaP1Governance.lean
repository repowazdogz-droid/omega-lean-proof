-- OMEGA Protocol - P1 Governance, concrete predicate
-- Goal contract reference: /Users/warre/Omega/unified-forge/goal-contract.md
-- Goal: lift P1 from an uninterpreted Prop atom (as it appears in
-- OmegaV14) to a concrete predicate over a Record, matching the
-- treatment of P3 in OmegaP3Semantic.
-- Non-goals: complete the proofs (use sorry initially; the priority is
-- getting the types right).
-- Verification: run `lake build` from /Users/warre/Omega/lean-proof.
-- Provenance inputs:
--   - /Users/warre/Omega/lean-proof/OmegaP3Semantic.lean
--   - /Users/warre/Omega/unified-forge/provenance-schema.json (review_status enum)
--   - /Users/warre/Omega/unified-forge/experiments/verification-extension-plan.md

import OmegaP3Semantic

namespace OmegaP1Governance

-- Reuse the Record structure from OmegaP3Semantic; both P1 and P3 are
-- predicates over the same underlying artefact.
open OmegaP3Semantic (Record)

/-- The four canonical review_status values, mirroring
    `unified-forge/provenance-schema.json`. -/
def valid_review_status (s : String) : Prop :=
  s = "pending" ∨ s = "accepted" ∨ s = "rejected" ∨ s = "escalated"

/--
P1 Governance, as a concrete predicate over a Record.

A record carries governance if and only if all three structural
attribution requirements hold:

1. `goal_contract_ref` is non-empty — the record names the goal contract
   under whose authority the work was performed.
2. `author_agent` is non-empty — the record names the entity that
   produced the artefact.
3. `review_status` is one of the four canonical enum values
   (`pending`, `accepted`, `rejected`, `escalated`).

Without all three, the record cannot be attributed to a known authority
chain and is not a governance-bearing artefact.
-/
def P1_Governance (r : Record) : Prop :=
  r.goal_contract_ref ≠ "" ∧
  r.author_agent ≠ "" ∧
  valid_review_status r.review_status

/-- If a record satisfies P1_Governance, its `goal_contract_ref` is
    non-empty. Trivially provable by projection; left as `sorry`
    intentionally so the type signature can be confirmed first. -/
theorem governance_requires_contract (r : Record) :
    P1_Governance r → r.goal_contract_ref ≠ "" := by
  sorry

/-- If a record satisfies P1_Governance, its `author_agent` is
    non-empty. Trivially provable by projection; left as `sorry`
    intentionally so the type signature can be confirmed first. -/
theorem governance_requires_agent (r : Record) :
    P1_Governance r → r.author_agent ≠ "" := by
  sorry

end OmegaP1Governance
