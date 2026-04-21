-- ============================================================
-- OMEGA Protocol v1.3 — Lean 4 Formal Verification
-- Bundle: v1.2 twelvefold core + P10–P12 + FAH + FAA (seventeen conjuncts).
-- Pure propositional scaffolding (no `sorry`, no custom axioms).
-- ============================================================

variable
  (P1 : Prop)   -- Governance
  (P2 : Prop)   -- Reasoning
  (P3 : Prop)   -- Traceability
  (P4 : Prop)   -- Expectation
  (P4M : Prop)   -- Materiality Binding
  (P4T : Prop)   -- Trajectory Expectation
  (P5 : Prop)   -- Confirmation
  (P5E : Prop)   -- Execution Attestation
  (P6 : Prop)   -- Delegation
  (P6A : Prop)   -- Aggregate Materiality
  (P6L : Prop)   -- Liability Threshold
  (PCF : Prop)   -- Continuity-Formal
  (P10 : Prop)   -- Competence Attestation (v1.3)
  (P11 : Prop)   -- Expectation Update Integrity (v1.3)
  (P12 : Prop)   -- Semantic Integrity Validation (v1.3)
  (FAH : Prop)   -- Accountability Horizon (honest limit)
  (FAA : Prop)   -- Attestation Authority Integrity (honest limit)

def Governed :=
  P1 ∧ P2 ∧ P3 ∧ P4 ∧ P4M ∧ P4T ∧ P5 ∧ P5E ∧ P6 ∧ P6A ∧ P6L ∧ PCF ∧ P10 ∧ P11 ∧ P12 ∧ FAH ∧ FAA

-- NECESSITY: Governed implies each conjunct

theorem p1_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA → P1 :=
  fun h => h.1

theorem p2_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA → P2 :=
  fun h => h.2.1

theorem p3_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA → P3 :=
  fun h => h.2.2.1

theorem p4_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA → P4 :=
  fun h => h.2.2.2.1

theorem p4m_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA → P4M :=
  fun h => h.2.2.2.2.1

theorem p4t_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA → P4T :=
  fun h => h.2.2.2.2.2.1

theorem p5_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA → P5 :=
  fun h => h.2.2.2.2.2.2.1

theorem p5e_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA → P5E :=
  fun h => h.2.2.2.2.2.2.2.1

theorem p6_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA → P6 :=
  fun h => h.2.2.2.2.2.2.2.2.1

theorem p6a_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA → P6A :=
  fun h => h.2.2.2.2.2.2.2.2.2.1

theorem p6l_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA → P6L :=
  fun h => h.2.2.2.2.2.2.2.2.2.2.1

theorem pcf_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA → PCF :=
  fun h => h.2.2.2.2.2.2.2.2.2.2.2.1

theorem p10_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA → P10 :=
  fun h => h.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem p11_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA → P11 :=
  fun h => h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem p12_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA → P12 :=
  fun h => h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem fah_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA → FAH :=
  fun h => h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem faa_necessary :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA → FAA :=
  fun h => h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

-- SUFFICIENCY: all conjuncts together

theorem all_governed_conjuncts_sufficient
    (p1 : P1) (p2 : P2) (p3 : P3) (p4 : P4) (p4m : P4M) (p4t : P4T) (p5 : P5) (p5e : P5E) (p6 : P6) (p6a : P6A) (p6l : P6L) (pcf : PCF) (p10 : P10) (p11 : P11) (p12 : P12) (fah : FAH) (faa : FAA) :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  ⟨p1, p2, p3, p4, p4m, p4t, p5, p5e, p6, p6a, p6l, pcf, p10, p11, p12, fah, faa⟩

-- ABSENCE: omitting any conjunct contradicts Governed

theorem p1_absent_governed_false :
    ¬ P1 → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  fun h_not h_gov => h_not (p1_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA h_gov)

theorem p2_absent_governed_false :
    ¬ P2 → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  fun h_not h_gov => h_not (p2_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA h_gov)

theorem p3_absent_governed_false :
    ¬ P3 → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  fun h_not h_gov => h_not (p3_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA h_gov)

theorem p4_absent_governed_false :
    ¬ P4 → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  fun h_not h_gov => h_not (p4_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA h_gov)

theorem p4m_absent_governed_false :
    ¬ P4M → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  fun h_not h_gov => h_not (p4m_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA h_gov)

theorem p4t_absent_governed_false :
    ¬ P4T → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  fun h_not h_gov => h_not (p4t_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA h_gov)

theorem p5_absent_governed_false :
    ¬ P5 → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  fun h_not h_gov => h_not (p5_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA h_gov)

theorem p5e_absent_governed_false :
    ¬ P5E → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  fun h_not h_gov => h_not (p5e_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA h_gov)

theorem p6_absent_governed_false :
    ¬ P6 → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  fun h_not h_gov => h_not (p6_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA h_gov)

theorem p6a_absent_governed_false :
    ¬ P6A → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  fun h_not h_gov => h_not (p6a_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA h_gov)

theorem p6l_absent_governed_false :
    ¬ P6L → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  fun h_not h_gov => h_not (p6l_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA h_gov)

theorem pcf_absent_governed_false :
    ¬ PCF → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  fun h_not h_gov => h_not (pcf_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA h_gov)

theorem p10_absent_governed_false :
    ¬ P10 → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  fun h_not h_gov => h_not (p10_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA h_gov)

theorem p11_absent_governed_false :
    ¬ P11 → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  fun h_not h_gov => h_not (p11_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA h_gov)

theorem p12_absent_governed_false :
    ¬ P12 → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  fun h_not h_gov => h_not (p12_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA h_gov)

theorem fah_absent_governed_false :
    ¬ FAH → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  fun h_not h_gov => h_not (fah_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA h_gov)

theorem faa_absent_governed_false :
    ¬ FAA → ¬ Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  fun h_not h_gov => h_not (faa_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA h_gov)

-- BICONDITIONAL: definitional unfolding

theorem governed_iff_all_conjuncts :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA ↔
    P1 ∧ P2 ∧ P3 ∧ P4 ∧ P4M ∧ P4T ∧ P5 ∧ P5E ∧ P6 ∧ P6A ∧ P6L ∧ PCF ∧ P10 ∧ P11 ∧ P12 ∧ FAH ∧ FAA :=
  Iff.rfl

-- Authorisation bundle (explicit witness packaging)

theorem authorisation_condition
    (p1 : P1) (p2 : P2) (p3 : P3) (p4 : P4) (p4m : P4M) (p4t : P4T) (p5 : P5) (p5e : P5E) (p6 : P6) (p6a : P6A) (p6l : P6L) (pcf : PCF) (p10 : P10) (p11 : P11) (p12 : P12) (fah : FAH) (faa : FAA) :
    Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA :=
  all_governed_conjuncts_sufficient P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF P10 P11 P12 FAH FAA
  p1 p2 p3 p4 p4m p4t p5 p5e p6 p6a p6l pcf p10 p11 p12 fah faa

-- Silence is the result.
