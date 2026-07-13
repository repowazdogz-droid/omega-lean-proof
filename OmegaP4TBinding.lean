/-
═══════════════════════════════════════════════════════════════════════════
OMEGA — P4T_EnvInvariant SEMANTIC BINDING
═══════════════════════════════════════════════════════════════════════════

PURPOSE.  Give the P4T_EnvInvariant conjunct of the shipped 22-way
`OmegaV14.Governed` bundle real verified semantic content, additively, the same
way `OmegaP6ABinding.lean` did for P6A. In `OmegaV14.lean`, P4T_EnvInvariant is an
uninterpreted `variable (P4T_EnvInvariant : Prop)`: "Trajectory commitments must
declare environmental invariants under which the commitment is valid; violation of
the invariant automatically invalidates the trajectory."

PROPERTY TYPE.  A state-validity property local to each prediction: a pre-committed
trajectory prediction holds only WHILE its declared environment assumption remains
true; if the assumption is invalidated, the prediction is revoked. This is a clean
`rfl`/`decide` fit (no aggregate, no induction) — the "comfortable local check"
(the prediction was validly committed) is blind to whether the environment still
holds, and an env-invariant guard decides it.

TRUST BASE.  Lean kernel, v4.27.0, ZERO user axioms (confirmed by `#print axioms`
below). MODEL-LEVEL only: the env-invariant property holds in this model and
P4T_EnvInvariant can stand for it; this makes NO claim that a deployed trajectory
system matches the model.

ADDITIVE.  No shipped file modified. Not a Lake root; checked with
`lake env lean OmegaP4TBinding.lean`. Imports the real shipped `OmegaV14`.
-/

import OmegaV14

namespace OmegaP4TBinding

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 1 — the environment-invariant model
-- ═══════════════════════════════════════════════════════════════════════════

/-- A pre-committed trajectory prediction: whether its declared environment
    invariant currently holds, and whether the prediction is being treated as
    in-force. -/
structure Prediction where
  assumptionHolds : Bool   -- the declared environmental invariant is currently satisfied
  claimed         : Bool   -- the prediction is being treated as still in-force
  deriving DecidableEq, Repr

/-- The blind local check: the prediction was validly committed (it records a
    declared assumption). True regardless of the current environment — it cannot
    see that the assumption has since been invalidated. -/
def committed (_ : Prediction) : Bool := true

/-- Forbidden behaviour: the prediction is treated as holding (`claimed`) AFTER its
    declared environment assumption has been invalidated (`¬assumptionHolds`). -/
@[reducible] def StaleHeld (p : Prediction) : Prop :=
  (p.claimed && !p.assumptionHolds) = true

/-- The env-invariant guard's decision: the same stale condition — the prediction is
    in force while its assumption is false. (Decides `StaleHeld` by `Iff.rfl`-defeq.) -/
@[reducible] def decStale (p : Prediction) : Prop :=
  (p.claimed && !p.assumptionHolds) = true

/-- The repaired relation: committed AND not stale — a prediction in force only while
    its declared environment invariant holds. -/
def EnvRepaired (p : Prediction) : Prop := committed p = true ∧ ¬ decStale p

/-- Witness: assumption invalidated, prediction still treated as in-force. -/
def witnessPred : Prediction := ⟨false, true⟩

/-- Benign partner: assumption holds, prediction in force. Same committed verdict. -/
def benignPred : Prediction := ⟨true, true⟩

/-- THE HEART OF P4T_EnvInvariant: the local "validly committed" check passes, yet the
    prediction is held after its environment assumption was invalidated. A valid
    commitment does not imply current validity. -/
theorem env_stale_local_insufficient :
    committed witnessPred = true ∧ StaleHeld witnessPred :=
  ⟨rfl, rfl⟩

/-- THE REPAIR: the env-invariant guard removes every stale-held witness — if the
    declared assumption no longer holds, the prediction is revoked. -/
theorem env_invariant_removes_witness :
    ∀ p, EnvRepaired p → ¬ StaleHeld p := by
  intro p hC hV
  exact hC.2 hV

/-- The repair is not vacuous: a prediction whose declared assumptions still hold is
    accepted. -/
theorem env_invariant_not_vacuous : EnvRepaired benignPred :=
  ⟨rfl, by decide⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 2 — the concrete predicate that P4T_EnvInvariant stands for
-- ═══════════════════════════════════════════════════════════════════════════

/-- The SEMANTIC CONTENT of P4T_EnvInvariant: (1) a valid commitment does not imply
    current validity — a prediction held after its environment assumption was
    invalidated, passing the local check; (2) the env-invariant guard revokes every
    such prediction; (3) the guard still accepts predictions whose assumptions hold. -/
def P4T_Concrete : Prop :=
  (committed witnessPred = true ∧ StaleHeld witnessPred)
  ∧ (∀ p, EnvRepaired p → ¬ StaleHeld p)
  ∧ EnvRepaired benignPred

/-- `P4T_Concrete` HOLDS — kernel-checked, axiom-free. -/
theorem p4t_concrete_holds : P4T_Concrete :=
  ⟨env_stale_local_insufficient, env_invariant_removes_witness, env_invariant_not_vacuous⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 3 — the binding to the shipped bundle (slot 21: P4T_EnvInvariant)
-- ═══════════════════════════════════════════════════════════════════════════

/-- SUFFICIENCY, with P4T_EnvInvariant made concrete: `Governed` holds with that slot
    set to `P4T_Concrete`, discharged by `p4t_concrete_holds` rather than assumed,
    needing only the other 21 atoms as hypotheses. -/
theorem governed_p4t_env_instantiated
    (P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF : Prop)
    (P10 P11 P12 FAH FAA : Prop)
    (P2_DAG P6_AtomicAgency P1_Freshness P_ChainIntegrity : Prop)
    (p1 : P1) (p2 : P2) (p3 : P3) (p4 : P4) (p4m : P4M) (p4t : P4T)
    (p5 : P5) (p5e : P5E) (p6 : P6) (p6a : P6A) (p6l : P6L) (pcf : PCF)
    (p10 : P10) (p11 : P11) (p12 : P12) (fah : FAH) (faa : FAA)
    (p2dag : P2_DAG) (p6atom : P6_AtomicAgency) (p1fr : P1_Freshness)
    (pchain : P_ChainIntegrity) :
    OmegaV14.Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_Concrete
      P_ChainIntegrity :=
  OmegaV14.all_twentytwo_conjuncts_sufficient
    P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_Concrete
    P_ChainIntegrity
    p1 p2 p3 p4 p4m p4t p5 p5e p6 p6a p6l pcf
    p10 p11 p12 fah faa p2dag p6atom p1fr p4t_concrete_holds pchain

/-- NECESSITY, recovered at the concrete instance: the bundle instantiated at
    `P4T_Concrete` hands the property back out (slot 21, the same projection the
    bundle's own `p4t_envinvariant_necessary` uses). -/
theorem p4t_concrete_necessary
    (P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF : Prop)
    (P10 P11 P12 FAH FAA : Prop)
    (P2_DAG P6_AtomicAgency P1_Freshness P_ChainIntegrity : Prop) :
    OmegaV14.Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_Concrete
      P_ChainIntegrity
    → P4T_Concrete :=
  fun h => h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

-- ═══════════════════════════════════════════════════════════════════════════
-- AXIOM AUDIT
-- ═══════════════════════════════════════════════════════════════════════════

#print axioms env_stale_local_insufficient
#print axioms env_invariant_removes_witness
#print axioms env_invariant_not_vacuous
#print axioms p4t_concrete_holds
#print axioms governed_p4t_env_instantiated
#print axioms p4t_concrete_necessary

end OmegaP4TBinding
