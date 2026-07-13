/-
═══════════════════════════════════════════════════════════════════════════
OMEGA — P4M (Materiality Binding) SEMANTIC BINDING  [Lean, zero-axiom]
═══════════════════════════════════════════════════════════════════════════
Additive binding of the P4M conjunct of OmegaV14.Governed (slot 5). P4M:
"Materiality Binding" — an expectation must be bound to a materiality
assessment; an expectation whose consequence is material (>= threshold) must
carry that binding (be flagged), or its downstream gates (P6A/P6L) are blind.

Property type: per-expectation threshold/completeness — a clean rfl/decide
Lean fit (same shape as the P6L liability binding). The blind local check ("a
record exists") is blind to whether materiality is bound; a material expectation
left unbound passes it; the materiality-binding rule removes it; a properly
bound (or immaterial) expectation is still accepted.

TRUST BASE: Lean kernel v4.27.0, ZERO user axioms (#print axioms below).
MODEL-LEVEL only; no claim a deployed system matches the model.
ADDITIVE: not a Lake root; `lake env lean OmegaP4MBinding.lean`; imports real OmegaV14.
-/
import OmegaV14
namespace OmegaP4MBinding

structure Expectation where
  materiality : Nat    -- consequence magnitude (0 = none/unassessed)
  flagged     : Bool   -- materiality assessment attached / flagged material
  deriving DecidableEq, Repr

def matThreshold : Nat := 2   -- at/above this, the expectation is material

/-- Blind local check: a record for the expectation exists. Blind to whether a
    materiality binding is attached. -/
def recorded (_ : Expectation) : Bool := true

/-- Forbidden: the expectation is material (materiality >= threshold) yet not
    flagged — materiality left unbound. -/
@[reducible] def Unbound (e : Expectation) : Prop :=
  (Nat.ble matThreshold e.materiality && !e.flagged) = true

/-- Repaired relation: recorded AND not materially-unbound. -/
def MatRepaired (e : Expectation) : Prop := recorded e = true ∧ ¬ Unbound e

def witnessExp : Expectation := ⟨3, false⟩   -- material (3 ≥ 2), not flagged
def benignExp  : Expectation := ⟨3, true⟩    -- material AND flagged (bound)

/-- HEART: a material expectation passes the "recorded" check yet is unbound. -/
theorem material_unbound_insufficient :
    recorded witnessExp = true ∧ Unbound witnessExp := ⟨rfl, rfl⟩

/-- REPAIR: the materiality-binding rule removes every unbound-material witness. -/
theorem materiality_binding_removes_witness :
    ∀ e, MatRepaired e → ¬ Unbound e := by
  intro e hC hV; exact hC.2 hV

/-- NON-VACUITY: a properly bound material expectation is still accepted. -/
theorem materiality_binding_not_vacuous : MatRepaired benignExp := ⟨rfl, by decide⟩

def P4M_Concrete : Prop :=
  (recorded witnessExp = true ∧ Unbound witnessExp)
  ∧ (∀ e, MatRepaired e → ¬ Unbound e)
  ∧ MatRepaired benignExp

theorem p4m_concrete_holds : P4M_Concrete :=
  ⟨material_unbound_insufficient, materiality_binding_removes_witness, materiality_binding_not_vacuous⟩

/-- SUFFICIENCY with P4M made concrete (slot 5), discharged not assumed. -/
theorem governed_p4m_instantiated
    (P1 P2 P3 P4 P4T P5 P5E P6 P6A P6L PCF : Prop)
    (P10 P11 P12 FAH FAA : Prop)
    (P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity : Prop)
    (p1 : P1) (p2 : P2) (p3 : P3) (p4 : P4) (p4t : P4T)
    (p5 : P5) (p5e : P5E) (p6 : P6) (p6a : P6A) (p6l : P6L) (pcf : PCF)
    (p10 : P10) (p11 : P11) (p12 : P12) (fah : FAH) (faa : FAA)
    (p2dag : P2_DAG) (p6atom : P6_AtomicAgency) (p1fr : P1_Freshness)
    (p4tenv : P4T_EnvInvariant) (pchain : P_ChainIntegrity) :
    OmegaV14.Governed P1 P2 P3 P4 P4M_Concrete P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity :=
  OmegaV14.all_twentytwo_conjuncts_sufficient
    P1 P2 P3 P4 P4M_Concrete P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
    P_ChainIntegrity
    p1 p2 p3 p4 p4m_concrete_holds p4t p5 p5e p6 p6a p6l pcf
    p10 p11 p12 fah faa p2dag p6atom p1fr p4tenv pchain

/-- NECESSITY at the concrete instance (slot 5 projection). -/
theorem p4m_concrete_necessary
    (P1 P2 P3 P4 P4T P5 P5E P6 P6A P6L PCF : Prop)
    (P10 P11 P12 FAH FAA : Prop)
    (P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity : Prop) :
    OmegaV14.Governed P1 P2 P3 P4 P4M_Concrete P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity
    → P4M_Concrete :=
  fun h => h.2.2.2.2.1

#print axioms material_unbound_insufficient
#print axioms materiality_binding_removes_witness
#print axioms materiality_binding_not_vacuous
#print axioms p4m_concrete_holds
#print axioms governed_p4m_instantiated
#print axioms p4m_concrete_necessary

end OmegaP4MBinding
