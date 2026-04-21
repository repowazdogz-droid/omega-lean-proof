-- ============================================================
-- OMEGA Protocol v1.2 — Lean 4 Formal Verification
-- Twelve primitives necessary and sufficient
-- April 2026
-- Expected result: no errors, no warnings. Silence is the result.
-- ============================================================

variable
  (P1 : Prop)   -- Governance
  (P2 : Prop)   -- Reasoning
  (P3 : Prop)   -- Traceability
  (P4 : Prop)   -- Expectation
  (P4M : Prop)  -- Materiality Binding
  (P4T : Prop)  -- Trajectory Expectation
  (P5 : Prop)   -- Confirmation
  (P5E : Prop)  -- Execution Attestation
  (P6 : Prop)   -- Delegation
  (P6A : Prop)  -- Aggregate Materiality
  (P6L : Prop)  -- Liability Threshold
  (PCF : Prop)  -- Continuity-Formal

def Governed :=
  P1 ∧ P2 ∧ P3 ∧ P4 ∧ P4M ∧ P4T ∧ P5 ∧ P5E ∧ P6 ∧ P6A ∧ P6L ∧ PCF

-- NECESSITY: Governed implies each primitive

theorem p1_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF → P1 :=
  fun h => h.1

theorem p2_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF → P2 :=
  fun h => h.2.1

theorem p3_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF → P3 :=
  fun h => h.2.2.1

theorem p4_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF → P4 :=
  fun h => h.2.2.2.1

theorem p4m_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF → P4M :=
  fun h => h.2.2.2.2.1

theorem p4t_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF → P4T :=
  fun h => h.2.2.2.2.2.1

theorem p5_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF → P5 :=
  fun h => h.2.2.2.2.2.2.1

theorem p5e_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF → P5E :=
  fun h => h.2.2.2.2.2.2.2.1

theorem p6_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF → P6 :=
  fun h => h.2.2.2.2.2.2.2.2.1

theorem p6a_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF → P6A :=
  fun h => h.2.2.2.2.2.2.2.2.2.1

theorem p6l_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF → P6L :=
  fun h => h.2.2.2.2.2.2.2.2.2.2.1

theorem pcf_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF → PCF :=
  fun h => h.2.2.2.2.2.2.2.2.2.2.2

-- SUFFICIENCY: all twelve together produce Governed

theorem all_twelve_sufficient
    (p1 : P1) (p2 : P2) (p3 : P3) (p4 : P4)
    (p4m : P4M) (p4t : P4T) (p5 : P5) (p5e : P5E)
    (p6 : P6) (p6a : P6A) (p6l : P6L) (pcf : PCF) :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF :=
  ⟨p1, p2, p3, p4, p4m, p4t, p5, p5e, p6, p6a, p6l, pcf⟩

-- ABSENCE THEOREMS: each primitive individually necessary

theorem p1_absent_governed_false :
    ¬ P1 → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF :=
  fun h_not h_gov => h_not (p1_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF h_gov)

theorem p2_absent_governed_false :
    ¬ P2 → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF :=
  fun h_not h_gov => h_not (p2_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF h_gov)

theorem p3_absent_governed_false :
    ¬ P3 → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF :=
  fun h_not h_gov => h_not (p3_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF h_gov)

theorem p4_absent_governed_false :
    ¬ P4 → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF :=
  fun h_not h_gov => h_not (p4_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF h_gov)

theorem p4m_absent_governed_false :
    ¬ P4M → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF :=
  fun h_not h_gov => h_not (p4m_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF h_gov)

theorem p4t_absent_governed_false :
    ¬ P4T → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF :=
  fun h_not h_gov => h_not (p4t_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF h_gov)

theorem p5_absent_governed_false :
    ¬ P5 → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF :=
  fun h_not h_gov => h_not (p5_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF h_gov)

theorem p5e_absent_governed_false :
    ¬ P5E → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF :=
  fun h_not h_gov => h_not (p5e_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF h_gov)

theorem p6_absent_governed_false :
    ¬ P6 → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF :=
  fun h_not h_gov => h_not (p6_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF h_gov)

theorem p6a_absent_governed_false :
    ¬ P6A → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF :=
  fun h_not h_gov => h_not (p6a_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF h_gov)

theorem p6l_absent_governed_false :
    ¬ P6L → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF :=
  fun h_not h_gov => h_not (p6l_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF h_gov)

theorem pcf_absent_governed_false :
    ¬ PCF → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF :=
  fun h_not h_gov => h_not (pcf_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF h_gov)

-- BICONDITIONAL: Governed iff all twelve

theorem governed_iff_all_twelve :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF ↔
    P1 ∧ P2 ∧ P3 ∧ P4 ∧ P4M ∧ P4T ∧ P5 ∧ P5E ∧ P6 ∧ P6A ∧ P6L ∧ PCF :=
  Iff.rfl

-- THE AUTHORISATION CONDITION
-- A(α) = G ∧ R ∧ T ∧ E ∧ P4M ∧ P4T ∧ C ∧ P5E ∧ P6 ∧ P6A ∧ P6L ∧ PCF

theorem authorisation_condition
    (p1 : P1) (p2 : P2) (p3 : P3) (p4 : P4)
    (p4m : P4M) (p4t : P4T) (p5 : P5) (p5e : P5E)
    (p6 : P6) (p6a : P6A) (p6l : P6L) (pcf : PCF) :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF :=
  all_twelve_sufficient P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    p1 p2 p3 p4 p4m p4t p5 p5e p6 p6a p6l pcf

-- Silence is the result.
