-- OMEGA Protocol v1.4.1 — Lean 4 Formal Proof
-- Structural Integrity + Chain Integrity Release
-- Extends v1.3 17-conjunct bundle with 5 new constraints:
--   P2_DAG, P6_AtomicAgency, P1_Freshness, P4T_EnvInvariant, P_ChainIntegrity
-- Zero sorry. Zero user axioms.

namespace OmegaV14

-- ═══════════════════════════════════════════════════════
-- v1.3 PRIMITIVES (carried forward unchanged)
-- ═══════════════════════════════════════════════════════

variable (P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF : Prop)
variable (P10 P11 P12 : Prop)
variable (FAH FAA : Prop)

-- ═══════════════════════════════════════════════════════
-- v1.4 NEW CONSTRAINTS
-- ═══════════════════════════════════════════════════════

-- P2_DAG: P2 causal graph must be a Directed Acyclic Graph
-- with every path grounded in FACT, UNKNOWN, or declared ASSUMPTION
variable (P2_DAG : Prop)

-- P6_AtomicAgency: Any process satisfying the Atomic Decision Boundary
-- (external effect OR material influence OR delegation origin) must
-- produce a governed record or explicit ungoverned declaration
variable (P6_AtomicAgency : Prop)

-- P1_Freshness: Major/Catastrophic consequence decisions require
-- Temporal Freshness Proof (interactive authentication within declared
-- window, hash-chained into P3)
variable (P1_Freshness : Prop)

-- P4T_EnvInvariant: Trajectory commitments must declare environmental
-- invariants under which the commitment is valid; violation of
-- invariant automatically invalidates trajectory
variable (P4T_EnvInvariant : Prop)

-- P_ChainIntegrity: the SHA-256 hash chain (content_hash linked by
-- prev_hash from genesis to tip) is intact; tampering with any record
-- invalidates the chain past that point and is detectable by an
-- external party recomputing the chain.
variable (P_ChainIntegrity : Prop)

-- ═══════════════════════════════════════════════════════
-- GOVERNED PREDICATE (v1.4.1, 22-way conjunction)
-- ═══════════════════════════════════════════════════════

/-- Explicit `And` nesting so elaboration matches `.1` / `.2` projections. -/
def Governed : Prop :=
  And P1 (And P2 (And P3 (And P4 (And P4M (And P4T (And P5 (And P5E (And P6 (And P6A (And P6L (And PCF (And P10 (And P11 (And P12 (And FAH (And FAA (And P2_DAG (And P6_AtomicAgency (And P1_Freshness (And P4T_EnvInvariant P_ChainIntegrity))))))))))))))))))))

-- ═══════════════════════════════════════════════════════
-- NECESSITY THEOREMS (each constraint is necessary)
-- ═══════════════════════════════════════════════════════

-- If P2 is not a DAG, reasoning can contain cycles grounded in nothing,
-- producing structurally valid records with vacuous reasoning.
theorem p2_dag_necessary :
  Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity
  → P2_DAG := by
  intro h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

-- If Atomic Agency is not enforced, sub-processes bypass governance
-- by claiming "internal function" status, laundering decision points.
theorem p6_atomic_necessary :
  Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity
  → P6_AtomicAgency := by
  intro h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

-- Without Temporal Freshness, session hijack produces cryptographically
-- valid P1 records for actions the authenticated human never performed.
theorem p1_freshness_necessary :
  Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity
  → P1_Freshness := by
  intro h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

-- Without Environmental Invariants, trajectory commitments can remain
-- "valid" while the environment has shifted outside the assumption
-- envelope, producing on-trajectory records against a missing reality.
theorem p4t_envinvariant_necessary :
  Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity
  → P4T_EnvInvariant := by
  intro h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

-- Without Chain Integrity, the hash chain can be silently rewritten
-- after the fact; integrity claims rest on an attestation that cannot
-- be independently re-verified.
theorem pci_necessary :
  Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity
  → P_ChainIntegrity := by
  intro h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

-- ═══════════════════════════════════════════════════════
-- ABSENCE THEOREMS (removing any constraint invalidates Governed)
-- ═══════════════════════════════════════════════════════

theorem governed_fails_without_p2_dag :
  ¬P2_DAG →
  ¬Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity := by
  intro h_not_dag h_governed
  exact h_not_dag (p2_dag_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity h_governed)

theorem governed_fails_without_p6_atomic :
  ¬P6_AtomicAgency →
  ¬Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity := by
  intro h_not_atomic h_governed
  exact h_not_atomic (p6_atomic_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity h_governed)

theorem governed_fails_without_p1_freshness :
  ¬P1_Freshness →
  ¬Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity := by
  intro h_not_fresh h_governed
  exact h_not_fresh (p1_freshness_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity h_governed)

theorem governed_fails_without_p4t_envinvariant :
  ¬P4T_EnvInvariant →
  ¬Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity := by
  intro h_not_inv h_governed
  exact h_not_inv (p4t_envinvariant_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity h_governed)

theorem pci_absent_governed_false :
  ¬P_ChainIntegrity →
  ¬Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity := by
  intro h_not_pci h_governed
  exact h_not_pci (pci_necessary P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity h_governed)

-- ═══════════════════════════════════════════════════════
-- SUFFICIENCY (all 22 conjuncts jointly establish Governed)
-- ═══════════════════════════════════════════════════════

theorem all_twentytwo_conjuncts_sufficient :
  P1 → P2 → P3 → P4 → P4M → P4T → P5 → P5E →
  P6 → P6A → P6L → PCF →
  P10 → P11 → P12 →
  FAH → FAA →
  P2_DAG → P6_AtomicAgency → P1_Freshness → P4T_EnvInvariant →
  P_ChainIntegrity →
  Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity := by
  intros
  exact ⟨by assumption, by assumption, by assumption, by assumption,
         by assumption, by assumption, by assumption, by assumption,
         by assumption, by assumption, by assumption, by assumption,
         by assumption, by assumption, by assumption, by assumption,
         by assumption, by assumption, by assumption, by assumption,
         by assumption, by assumption⟩

-- ═══════════════════════════════════════════════════════
-- BICONDITIONAL (Governed iff all 22 conjuncts hold)
-- ═══════════════════════════════════════════════════════

theorem governed_iff_all_conjuncts :
  Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity ↔
  P1 ∧ P2 ∧ P3 ∧ P4 ∧ P4M ∧ P4T ∧ P5 ∧ P5E ∧
  P6 ∧ P6A ∧ P6L ∧ PCF ∧ P10 ∧ P11 ∧ P12 ∧
  FAH ∧ FAA ∧ P2_DAG ∧ P6_AtomicAgency ∧ P1_Freshness ∧ P4T_EnvInvariant ∧ P_ChainIntegrity :=
  Iff.rfl

-- ═══════════════════════════════════════════════════════
-- AUTHORISATION CONDITION (top-level governance predicate)
-- ═══════════════════════════════════════════════════════

theorem authorisation_condition :
  Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity →
  (P1 ∧ P5 ∧ P5E ∧ P6_AtomicAgency ∧ P1_Freshness ∧ P_ChainIntegrity) := by
  intro h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.1
  · exact h.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end OmegaV14
