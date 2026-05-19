-- OMEGA governance level partial order (Decision Gravity G1–G4)
-- Goal contract reference: /Users/warre/Omega/unified-forge/goal-contract.md
-- Verification: `lake build` from /Users/warre/Omega/lean-proof

namespace OmegaGovernance

/-- Decision gravity levels from the OMEGA runtime contract. -/
inductive GovernanceLevel : Type where
  | G1 | G2 | G3 | G4
  deriving DecidableEq, Repr

def GovernanceLevel.toNat : GovernanceLevel → Nat
  | .G1 => 1
  | .G2 => 2
  | .G3 => 3
  | .G4 => 4

def leGovernance (a b : GovernanceLevel) : Prop :=
  a.toNat ≤ b.toNat

instance : LE GovernanceLevel where
  le := leGovernance

theorem governance_level_refl :
    ∀ (g : GovernanceLevel), leGovernance g g := by
  intro g
  cases g <;> simp [leGovernance, GovernanceLevel.toNat]

theorem governance_level_transitive :
    ∀ (a b c : GovernanceLevel), leGovernance a b → leGovernance b c → leGovernance a c := by
  intro a b c hab hbc
  simp only [leGovernance] at hab hbc ⊢
  exact Nat.le_trans hab hbc

theorem governance_level_partial_order :
    ∀ (g : GovernanceLevel), g ≤ g := by
  intro g
  exact governance_level_refl g

theorem governance_level_antisymmetric :
    ∀ (a b : GovernanceLevel), leGovernance a b → leGovernance b a → a = b := by
  intro a b hab hba
  simp only [leGovernance, GovernanceLevel.toNat] at hab hba
  cases a <;> cases b <;> simp at hab hba ⊢ <;> rfl

end OmegaGovernance
