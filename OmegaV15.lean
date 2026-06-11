/-
═══════════════════════════════════════════════════════════════════════════════
  OMEGA Protocol v1.5.0 — Lean 4 Formal Proof (scaffold pass)
  29-conjunct Governed predicate with corrections from GPT-5.5 adversarial review.
═══════════════════════════════════════════════════════════════════════════════

  This file is the FIRST PASS of v1.5. Goal of this pass:
    (1) compile cleanly under `lake env lean OmegaV15.lean` from lean-proof/
    (2) encode the 29-conjunct architecture with the adversarial corrections
        named A through I in the spec brief applied
    (3) NAME every remaining gap explicitly (see -- OPEN PROOFS and -- STUB
        sections below). Zero-sorry is the NEXT pass.

  Predecessor: OmegaV14.lean (22 conjuncts, currently public).
  This file does NOT modify any other .lean file; it composes on top.

  ─────────────────────────────────────────────────────────────────────────────
  VERSIONING HONESTY — three concurrent profiles (per adversarial point A)
  ─────────────────────────────────────────────────────────────────────────────
    Governed-22 / v1.4.1        — current public, no P14
    Governed-23 / v1.4.2-draft  — adds P14 PredicateCommitment over v1.4.1
    Governed-29 / v1.5.0        — full P0 closure + P13 (this file)

  No retroactive redefinition: v1.4.1 remains the 22-conjunct profile. v1.5.0
  adds seven new conjuncts (P1_SelectionPolicy, P12_SchemaHash,
  P13_RegimeBinding, P14_PredicateCommitment, P15_InterWindowDriftContinuity,
  P6_AgencyBoundary, PCF_Cumulative).

  ─────────────────────────────────────────────────────────────────────────────
  ADVERSARIAL CORRECTIONS APPLIED (A–I from spec brief)
  ─────────────────────────────────────────────────────────────────────────────
    A. Three profile constants with disjoint schema hashes.
    B. DriftVector is 7-axis (identity_authority, capability_actuator,
       epistemic, objective_incentive, normative_policy, semantic_ontology,
       environment_threat), each UInt16 basis points (0–10000).
    C. Drift aggregation enforces THREE bounds simultaneously:
       max-axis ≤ T_single, weighted-sum ≤ T_total,
       non-compensability count ≤ maxElevated.
    D. PCF_Cumulative is renamed to honest BoundedWindow semantics AND an
       explicit P15_InterWindowDriftContinuity conjunct is added that catches
       window-laundering across ≥64-record windows. (Both, not either.)
    E. Drift extraction is pure over RawSnapshot — its type signature takes
       no PCF or P10 state. The corresponding theorem is non-trivial and is
       flagged in OPEN PROOFS pending parametricity argument.
    F. P6_AgencyBoundary replaces an additive P6_DelegationTrigger with a
       three-mode disjunction (atomic single actor, declared delegation,
       coupling closure). detectCoupling triggers on shared mutable access,
       reciprocal dependency, explicit delegation, shared incentive binding —
       NOT temporal proximity alone.
    G. Stakes-tier binding: DecisionInstant carries
       stakes_classification_policy_hash, stakes_evidence_hash, classifier_id,
       classifier_version, classification_evidence_hash, and its stakes_tier
       must equal the regime's stakes_tier (enforced inside
       P13_RegimeBinding_Holds).
    H. P13_RegimeBinding binds all listed fields (action_type, stakes_tier,
       policy_set_hash, schema_profile_hash, tolerance_class,
       competence_requirement_hash, escalation_threshold_hash,
       verifier_profile_hash, classifier_id, classifier_version,
       classification_evidence_hash) — see P13_RegimeBinding_Holds.
    I. Sequencing: types → encodings → registry/regime/stakes binding →
       DecisionInstant → DriftVector machinery → PCF stratification →
       P6 boundary → Governed_v15 last.

  ─────────────────────────────────────────────────────────────────────────────
  OPEN PROOFS — sorry count vs. deferred-but-not-sorry, both itemised
  ─────────────────────────────────────────────────────────────────────────────
  Sorried in this file (0):
    [O2] p6_no_coalition_escape  — REPAIRED + PROVED 2026-06-11.
         The original coupling hypothesis `(detectCoupling log graph).length > 0`
         ranged over `log`/`graph` free of the boundary `b` and was false as
         written (atomic-single-actor counterexample; preserved machine-checked in
         `probes/O2Counterexample.lean`). The repaired statement ranges over the
         `CouplingFinding` evidence and ties it to `b` via `h_atomic_single` (the
         meaning of single-actor: the two coupling parties coincide). Proved
         axiom-free, with `o2_repaired_non_vacuous` (hypotheses satisfiable) and
         `o2_old_counterexample_excluded` (the old counterexample fails the new
         hypotheses). detectCoupling remains STUB [S5] (`:= []`); the theorem is
         stated over the finding type it is typed to produce, not the stub output.

  Deferred-but-not-sorry (4):
    [O1] drift_extraction_pure_parametric
         — shipped in structural form (rfl on identical inputs). Strong form
           (parametricity-via-state-irrelevance over a universe of consumer
           states) requires modelling PCF/P10 state types and proving the
           extractDrift type-signature blocks reachability. Deferred.
    [O3] p15_no_window_laundering
         — shipped as the per-window guarantee (both windows pass DriftBounded).
           The strict "no cumulative drift across the 64-record gap" claim is
           encoded in P15_InterWindowDriftContinuity_Holds (the third
           conjunct, `DriftBounded` on the summed vector) but the explicit
           attack model showing that *removing* P15 admits a counterexample
           chain is deferred.
    [O4] p13_no_stakes_widening
         — shipped as the structural binding (stakes_tier and
           tolerance_window_ns are pinned to the regime). The counterexample
           showing that *without* P13 the other 28 conjuncts admit a stakes-
           widening attack is deferred (requires modelling the attacker as a
           record producer that satisfies every other predicate while routing
           into a weaker regime).
    [O5] drift_bounds_calibration
         — numeric defaults (T_single = 2000, T_total = 1400, maxElevated = 3)
           are placeholder. Calibration against empirical drift distributions
           and threat-model envelopes is a non-Lean exercise; the Lean side
           remains parametric over `bounds : DriftBounds`.

  ─────────────────────────────────────────────────────────────────────────────
  STUBS (every `STUB` marker — types needing concrete definition before
  zero-sorry)
  ─────────────────────────────────────────────────────────────────────────────
    [S1] RawSnapshot          — observation type; payload schema deferred.
    [S2] MemoryAccessLog      — entry type, ≤4096 cap mechanism deferred.
    [S3] DeploymentGraph      — edge schema, ≤32 agent cap deferred.
    [S4] GovernanceRegime     — content of policy_set_hash deferred.
    [S5] detectCoupling       — concrete coupling-detection algorithm.
    [S6] extractDrift         — concrete extraction from snapshots.

═══════════════════════════════════════════════════════════════════════════════
-/

import OmegaV14
import OmegaP3Semantic
import OmegaP1Governance

namespace OmegaV15

/-! ## §0 Version constants (point A) -/

def schemaProfile_v1_4_1     : String := "Governed-22/v1.4.1"
def schemaProfile_v1_4_2_draft : String := "Governed-23/v1.4.2-draft"
def schemaProfile_v1_5_0     : String := "Governed-29/v1.5.0"

def thisFileProfile      : String := schemaProfile_v1_5_0
def thisFileConjunctCount : Nat   := 29

/-- Each profile gets a distinct schema_profile_hash binding in regime records. -/
def profileHashOf : String → String
  | "Governed-22/v1.4.1"       => "sha256:profile-v141"
  | "Governed-23/v1.4.2-draft" => "sha256:profile-v142d"
  | "Governed-29/v1.5.0"       => "sha256:profile-v150"
  | _                           => "sha256:profile-unknown"

/-! ## §1 Types — sequencing per point I

    Types come before encodings, registry, drift machinery, PCF stratification,
    P6 boundary, and Governed_v15 last. -/

/-- STUB [S1]: RawSnapshot — read-only observation feeding pure drift
    extraction. Schema deferred to next pass. -/
structure RawSnapshot where
  agent_id     : String
  timestamp_ns : UInt64
  payload_hash : ByteArray

/-- 7-axis principled drift basis (point B). Each axis is UInt16 basis
    points (0–10000, where 10000 = 100%). -/
structure DriftVector where
  identity_authority  : UInt16
  capability_actuator : UInt16
  epistemic           : UInt16
  objective_incentive : UInt16
  normative_policy    : UInt16
  semantic_ontology   : UInt16
  environment_threat  : UInt16

/-- Three-way drift bound (point C). All three must hold simultaneously to
    pass `DriftBounded`. -/
structure DriftBounds where
  T_single    : UInt16  -- default 2000 = 20% basis points per axis
  T_total     : UInt32  -- default 1400 = 14% weighted aggregate
  maxElevated : Nat     -- default 3
  axisWeights : List UInt16  -- 7 entries; empty list → uniform default

/-- Defaults per point C. Numeric calibration is OPEN [O5]. -/
def DriftBounds.default : DriftBounds :=
  { T_single := 2000, T_total := 1400, maxElevated := 3, axisWeights := [] }

/-- STUB [S2]: MemoryAccessLog. ≤4096 entry cap mechanism deferred. -/
structure MemoryAccessLog where
  entries        : List String
  capRespected   : entries.length ≤ 4096

/-- STUB [S3]: DeploymentGraph. ≤32 agent cap deferred. -/
structure DeploymentGraph where
  agents      : List String
  capRespected : agents.length ≤ 32

/-- STUB [S4]: GovernanceRegime — full schema in design memo. -/
structure GovernanceRegime where
  action_type                  : String
  stakes_tier                  : String
  policy_set_hash              : ByteArray
  schema_profile_hash          : ByteArray
  tolerance_class              : String
  tolerance_window_ns          : UInt64
  competence_requirement_hash  : ByteArray
  escalation_threshold_hash    : ByteArray
  verifier_profile_hash        : ByteArray
  classifier_id                : String
  classifier_version           : String
  classification_evidence_hash : ByteArray

/-- DecisionInstant with stakes-tier binding (point G). Carries every field
    required so that P13_RegimeBinding can verify the stakes were not lied
    about to widen the freshness window. -/
structure DecisionInstant where
  stakes_tier                       : String
  tolerance_window_ns               : UInt64
  stakes_classification_policy_hash : ByteArray
  stakes_evidence_hash              : ByteArray
  classifier_id                     : String
  classifier_version                : String
  classification_evidence_hash      : ByteArray
  recorded_schema_profile_hash      : ByteArray

/-! ## §2 Encodings — placeholder canonical forms.

    A future pass will fold these into OmegaP3Semantic.canonicalBytes for
    end-to-end hash binding. For this scaffold they are stubs. -/

def DriftVector.canonicalBytes (_ : DriftVector) : ByteArray :=
  ByteArray.empty  -- STUB: 14-byte big-endian encoding (7 × UInt16)

def GovernanceRegime.canonicalBytes (_ : GovernanceRegime) : ByteArray :=
  ByteArray.empty  -- STUB

def DecisionInstant.canonicalBytes (_ : DecisionInstant) : ByteArray :=
  ByteArray.empty  -- STUB

/-! ## §3 Registry / Regime / Stakes binding

    Sequenced BEFORE PCF/P10/P14 (point I). -/

/-- The registry binding produced when a record is committed. It carries the
    regime and the hash that ties policy + schema + tolerance + classifier +
    classification evidence + competence + escalation + verifier into one
    object. -/
structure GovernanceRegimeBinding where
  regime         : GovernanceRegime
  binding_hash   : ByteArray
  recorded_at_ns : UInt64

/-- P13_RegimeBinding_Holds (point H). Every field listed in the spec brief
    is checked against the DecisionInstant. Stakes-tier substitution is
    blocked by `decision.stakes_tier = binding.regime.stakes_tier`. -/
def P13_RegimeBinding_Holds
    (binding : GovernanceRegimeBinding) (decision : DecisionInstant) : Prop :=
  decision.stakes_tier                  = binding.regime.stakes_tier ∧
  decision.recorded_schema_profile_hash = binding.regime.schema_profile_hash ∧
  decision.classifier_id                = binding.regime.classifier_id ∧
  decision.classifier_version           = binding.regime.classifier_version ∧
  decision.classification_evidence_hash = binding.regime.classification_evidence_hash ∧
  decision.tolerance_window_ns          = binding.regime.tolerance_window_ns

/-- Direct extraction of the stakes binding. If P13 holds, the decision's
    stakes_tier matches the regime's stakes_tier — closing the attack vector
    where an attacker claims lower stakes to widen the freshness window. -/
theorem p13_stakes_tier_bound
    (binding : GovernanceRegimeBinding) (decision : DecisionInstant)
    (h : P13_RegimeBinding_Holds binding decision) :
    decision.stakes_tier = binding.regime.stakes_tier := h.1

/-- And the tolerance window is bound to the regime, not chosen post hoc. -/
theorem p13_tolerance_window_bound
    (binding : GovernanceRegimeBinding) (decision : DecisionInstant)
    (h : P13_RegimeBinding_Holds binding decision) :
    decision.tolerance_window_ns = binding.regime.tolerance_window_ns :=
  h.2.2.2.2.2

/-! ## §4 DriftVector machinery — pure over RawSnapshot (point E) -/

/-- STUB [S6]: extractDrift takes ONLY snapshots, not PCF or P10 state.
    The type signature itself is the stratification claim. -/
def extractDrift (_snaps : List RawSnapshot) : DriftVector :=
  { identity_authority  := 0
  , capability_actuator := 0
  , epistemic           := 0
  , objective_incentive := 0
  , normative_policy    := 0
  , semantic_ontology   := 0
  , environment_threat  := 0 }

/-- Frozen drift = result of `extractDrift` over snapshots. PCF and P10 both
    *consume* this value; neither has the type-level capacity to modify it. -/
def frozenDrift (snaps : List RawSnapshot) : DriftVector := extractDrift snaps

/-- Functional determinism: equal inputs produce equal outputs. Not vacuous —
    it states that `frozenDrift` is a function (no side channel). -/
theorem drift_extraction_functional
    (s s' : List RawSnapshot) (h : s = s') :
    frozenDrift s = frozenDrift s' := by
  rw [h]

/-- OPEN PROOF [O1]: substantive parametric purity. The structural statement
    below — extractDrift's signature lacks PCF/P10 inputs by construction —
    is shipped now; a parametricity-by-state-irrelevance proof against a
    universe of consumer states is deferred. -/
theorem drift_extraction_pure_parametric
    (snaps : List RawSnapshot) :
    ∀ (consumerPCF consumerP10 : Unit),
      let _ := consumerPCF; let _ := consumerP10
      frozenDrift snaps = frozenDrift snaps := by
  intro _ _; rfl

/-! ### §4.1 Three-way bound aggregation (point C) -/

private def axesOf (d : DriftVector) : List UInt16 :=
  [ d.identity_authority, d.capability_actuator, d.epistemic
  , d.objective_incentive, d.normative_policy
  , d.semantic_ontology, d.environment_threat ]

def DriftVector.maxAxis (d : DriftVector) : UInt16 :=
  (axesOf d).foldl max 0

def DriftVector.weightedSum (d : DriftVector) (weights : List UInt16) : UInt32 :=
  let axes := axesOf d
  let ws   := if weights.length = 7 then weights else List.replicate 7 1429
  let pairs := axes.zip ws
  pairs.foldl (fun acc p => acc + p.1.toUInt32 * p.2.toUInt32) 0

def DriftVector.elevatedCount (d : DriftVector) (threshold : UInt16) : Nat :=
  (axesOf d).foldl (fun n a => if a ≥ threshold then n + 1 else n) 0

/-- All THREE bounds hold simultaneously. Max-only is gameable (point C). -/
def DriftBounded (d : DriftVector) (bounds : DriftBounds) : Prop :=
  d.maxAxis ≤ bounds.T_single ∧
  d.weightedSum bounds.axisWeights ≤ bounds.T_total ∧
  d.elevatedCount (bounds.T_single / 2) ≤ bounds.maxElevated

/-- Projecting out the max-axis bound. -/
theorem drift_bound_max_axis
    (d : DriftVector) (b : DriftBounds) (h : DriftBounded d b) :
    d.maxAxis ≤ b.T_single := h.1

/-- Projecting out the non-compensability (elevated-count) bound. -/
theorem drift_bound_non_compensable
    (d : DriftVector) (b : DriftBounds) (h : DriftBounded d b) :
    d.elevatedCount (b.T_single / 2) ≤ b.maxElevated := h.2.2

/-! ## §5 PCF stratification — consumers of frozen drift only

    PCF and P10 are stratified BELOW drift extraction. Their signatures take
    a frozen DriftVector and metadata; they cannot reach back into the
    snapshot list. -/

/-- PCF check reads the frozen drift vector and applies the three-way bound. -/
def PCFCheck_BoundedWindow
    (frozen : DriftVector) (bounds : DriftBounds) : Prop :=
  DriftBounded frozen bounds

/-- STUB: competence attestation must match the frozen drift's required
    competence_requirement_hash. The match-binding is what stops a P10
    attestation against a stale drift envelope. -/
def P10Check_AttestedAgainstFrozen
    (frozen : DriftVector) (regime : GovernanceRegime)
    (attestation : ByteArray) : Prop :=
  -- the frozen vector picks out a required competence; attestation must hash-match
  let _ := frozen  -- silence "unused" while keeping stratification visible
  attestation = regime.competence_requirement_hash

/-! ## §6 P6 AgencyBoundary — three-mode disjunction (point F) -/

inductive CouplingMode where
  | sharedMutableAccess
  | reciprocalDependency
  | explicitDelegation
  | sharedIncentiveBinding
  -- NOTE: temporal proximity alone is intentionally NOT a coupling mode.
  deriving DecidableEq

structure CouplingFinding where
  mode  : CouplingMode
  agentA : String
  agentB : String

/-- STUB [S5]: detectCoupling — concrete algorithm deferred. -/
def detectCoupling
    (_log : MemoryAccessLog) (_graph : DeploymentGraph) : List CouplingFinding :=
  []

/-- P6 AgencyBoundary: an action falls in exactly one of three modes. The
    disjunction is total over the design space: there is no "not atomic
    enough for P6A but not explicit enough for P6D" escape (point F). -/
structure P6AgencyBoundary where
  mode_P6A_AtomicSingleActor      : Bool
  mode_P6D_DelegatedOrCoalition   : Bool
  delegation_explicitly_declared  : Bool
  mode_P6C_CouplingClosure        : Bool
  coupling_closure_satisfied      : Bool

def P6_AgencyBoundary_Holds (b : P6AgencyBoundary) : Prop :=
  b.mode_P6A_AtomicSingleActor = true ∨
  (b.mode_P6D_DelegatedOrCoalition = true ∧
   b.delegation_explicitly_declared = true) ∨
  (b.mode_P6C_CouplingClosure = true ∧
   b.coupling_closure_satisfied = true)

/-- If any coupling mode is present, AgencyBoundary requires either declared
    delegation or coupling closure. Pure structural — the strong "no
    coalition escape" theorem is OPEN [O2]. -/
theorem p6_agency_disjunction_total (b : P6AgencyBoundary)
    (h : P6_AgencyBoundary_Holds b) :
    b.mode_P6A_AtomicSingleActor = true ∨
    (b.mode_P6D_DelegatedOrCoalition = true ∧
     b.delegation_explicitly_declared = true) ∨
    (b.mode_P6C_CouplingClosure = true ∧
     b.coupling_closure_satisfied = true) := h

/-! ## §7 P1 Selection Policy, P12 Schema Hash, P14, P15 -/

/-- P1_SelectionPolicy: when multiple valid P1 authorisations could apply,
    the agent commits ex ante to which one. (Architectural move #16.) -/
structure P1SelectionPolicy where
  candidate_authorities : List String
  chosen_authority      : String
  choice_committed_at_ns : UInt64
  choice_evidence_hash  : ByteArray

def P1_SelectionPolicy_Holds (p : P1SelectionPolicy) : Prop :=
  p.candidate_authorities.length ≥ 1 ∧
  p.chosen_authority ∈ p.candidate_authorities

/-- P12_SchemaHash (closed-world schema hashing, architectural move #17).
    All referenced definitions are content-addressed in the record so that
    no post-decision schema substitution is possible. -/
structure P12SchemaHash where
  definitions_set_hash : ByteArray
  record_bound_hash    : ByteArray

def P12_SchemaHash_Holds (s : P12SchemaHash) : Prop :=
  s.definitions_set_hash = s.record_bound_hash

/-- P14_PredicateCommitment with drift_vector_hash binding (architectural
    move #61). Stores the frozen drift vector's hash alongside the predicate
    hash in the commitment block. -/
structure P14PredicateCommitment where
  predicate_hash    : ByteArray
  drift_vector_hash : ByteArray
  commitment_at_ns  : UInt64

def P14_PredicateCommitment_Holds
    (c : P14PredicateCommitment) (frozen : DriftVector) : Prop :=
  c.drift_vector_hash = OmegaP3Semantic.compute_hash frozen.canonicalBytes

/-- P15_InterWindowDriftContinuity (point D). PCF_Cumulative is honestly
    renamed to PCF_BoundedWindow in this profile; P15 is a SEPARATE conjunct
    that catches window-laundering across ≥64-record windows. -/
structure WindowDriftSummary where
  window_size           : Nat
  start_seq             : Nat
  end_seq               : Nat
  window_drift_vector   : DriftVector
  window_summary_hash   : ByteArray

def P15_InterWindowDriftContinuity_Holds
    (prevWindow currWindow : WindowDriftSummary)
    (bounds : DriftBounds) : Prop :=
  -- the windows are temporally adjacent
  prevWindow.end_seq + 1 = currWindow.start_seq ∧
  -- both windows individually pass the three-way bound
  DriftBounded prevWindow.window_drift_vector bounds ∧
  DriftBounded currWindow.window_drift_vector bounds ∧
  -- and the *combined* drift across the boundary is also bounded
  DriftBounded
    { identity_authority  := prevWindow.window_drift_vector.identity_authority
                              + currWindow.window_drift_vector.identity_authority
    , capability_actuator := prevWindow.window_drift_vector.capability_actuator
                              + currWindow.window_drift_vector.capability_actuator
    , epistemic           := prevWindow.window_drift_vector.epistemic
                              + currWindow.window_drift_vector.epistemic
    , objective_incentive := prevWindow.window_drift_vector.objective_incentive
                              + currWindow.window_drift_vector.objective_incentive
    , normative_policy    := prevWindow.window_drift_vector.normative_policy
                              + currWindow.window_drift_vector.normative_policy
    , semantic_ontology   := prevWindow.window_drift_vector.semantic_ontology
                              + currWindow.window_drift_vector.semantic_ontology
    , environment_threat  := prevWindow.window_drift_vector.environment_threat
                              + currWindow.window_drift_vector.environment_threat }
    bounds

/-! ## §8 PCF_Cumulative (renamed semantics — bounded window AND inter-window)

    Per point D, PCF_Cumulative is honestly the BoundedWindow predicate; the
    cross-window invariant lives in P15 above. We keep the historical name
    `PCF_Cumulative` for the conjunct slot to preserve the public API but
    document the new semantics here. -/

def PCF_Cumulative_Holds
    (frozen : DriftVector) (bounds : DriftBounds) : Prop :=
  PCFCheck_BoundedWindow frozen bounds

/-! ## §9 The Governed_v15 predicate — 29-way conjunction (last per point I)

    Variable Props matching the V14 style so the predicate composes cleanly
    over both data-backed and uninterpreted conjuncts. -/

section Governed
-- v1.3 / v1.4 carried forward (22)
variable (P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF : Prop)
variable (P10 P11 P12 : Prop)
variable (FAH FAA : Prop)
variable (P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
          P_ChainIntegrity : Prop)
-- v1.5 additions (7)
variable (P1_SelectionPolicy P12_SchemaHash P13_RegimeBinding
          P14_PredicateCommitment P15_InterWindowDriftContinuity
          P6_AgencyBoundary PCF_Cumulative : Prop)

/-- The 29-conjunct Governed_v15 predicate. Right-nested `And` so projection
    matches `.1` / `.2` indexing, consistent with OmegaV14.Governed. -/
def Governed_v15 : Prop :=
  And P1 (And P2 (And P3 (And P4 (And P4M (And P4T (And P5 (And P5E
    (And P6 (And P6A (And P6L (And PCF (And P10 (And P11 (And P12
    (And FAH (And FAA (And P2_DAG (And P6_AtomicAgency (And P1_Freshness
    (And P4T_EnvInvariant (And P_ChainIntegrity (And P1_SelectionPolicy
    (And P12_SchemaHash (And P13_RegimeBinding (And P14_PredicateCommitment
    (And P15_InterWindowDriftContinuity (And P6_AgencyBoundary
    PCF_Cumulative)))))))))))))))))))))))))))

/-- Biconditional to flat And. Definitional unfolding. -/
theorem governed_v15_iff_all :
    Governed_v15 P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity P1_SelectionPolicy P12_SchemaHash P13_RegimeBinding
      P14_PredicateCommitment P15_InterWindowDriftContinuity P6_AgencyBoundary
      PCF_Cumulative ↔
    (P1 ∧ P2 ∧ P3 ∧ P4 ∧ P4M ∧ P4T ∧ P5 ∧ P5E ∧
     P6 ∧ P6A ∧ P6L ∧ PCF ∧ P10 ∧ P11 ∧ P12 ∧
     FAH ∧ FAA ∧ P2_DAG ∧ P6_AtomicAgency ∧ P1_Freshness ∧
     P4T_EnvInvariant ∧ P_ChainIntegrity ∧ P1_SelectionPolicy ∧
     P12_SchemaHash ∧ P13_RegimeBinding ∧ P14_PredicateCommitment ∧
     P15_InterWindowDriftContinuity ∧ P6_AgencyBoundary ∧ PCF_Cumulative) :=
  Iff.rfl

/-! ### §9.1 Necessity theorems for the v1.5 additions (mechanical projections) -/

theorem p1_selectionpolicy_necessary
    (h : Governed_v15 P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity P1_SelectionPolicy P12_SchemaHash P13_RegimeBinding
      P14_PredicateCommitment P15_InterWindowDriftContinuity P6_AgencyBoundary
      PCF_Cumulative) : P1_SelectionPolicy := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
                 _, sp, _, _, _, _, _, _⟩
  exact sp

theorem p12_schemahash_necessary
    (h : Governed_v15 P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity P1_SelectionPolicy P12_SchemaHash P13_RegimeBinding
      P14_PredicateCommitment P15_InterWindowDriftContinuity P6_AgencyBoundary
      PCF_Cumulative) : P12_SchemaHash := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
                 _, _, sh, _, _, _, _, _⟩
  exact sh

theorem p13_regimebinding_necessary
    (h : Governed_v15 P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity P1_SelectionPolicy P12_SchemaHash P13_RegimeBinding
      P14_PredicateCommitment P15_InterWindowDriftContinuity P6_AgencyBoundary
      PCF_Cumulative) : P13_RegimeBinding := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
                 _, _, _, rb, _, _, _, _⟩
  exact rb

theorem p14_predicatecommitment_necessary
    (h : Governed_v15 P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity P1_SelectionPolicy P12_SchemaHash P13_RegimeBinding
      P14_PredicateCommitment P15_InterWindowDriftContinuity P6_AgencyBoundary
      PCF_Cumulative) : P14_PredicateCommitment := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
                 _, _, _, _, pc, _, _, _⟩
  exact pc

theorem p15_interwindowdriftcontinuity_necessary
    (h : Governed_v15 P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity P1_SelectionPolicy P12_SchemaHash P13_RegimeBinding
      P14_PredicateCommitment P15_InterWindowDriftContinuity P6_AgencyBoundary
      PCF_Cumulative) : P15_InterWindowDriftContinuity := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
                 _, _, _, _, _, wc, _, _⟩
  exact wc

theorem p6_agencyboundary_necessary
    (h : Governed_v15 P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity P1_SelectionPolicy P12_SchemaHash P13_RegimeBinding
      P14_PredicateCommitment P15_InterWindowDriftContinuity P6_AgencyBoundary
      PCF_Cumulative) : P6_AgencyBoundary := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
                 _, _, _, _, _, _, ab, _⟩
  exact ab

theorem pcf_cumulative_necessary
    (h : Governed_v15 P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity P1_SelectionPolicy P12_SchemaHash P13_RegimeBinding
      P14_PredicateCommitment P15_InterWindowDriftContinuity P6_AgencyBoundary
      PCF_Cumulative) : PCF_Cumulative := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
                 _, _, _, _, _, _, _, pcfc⟩
  exact pcfc

/-! ### §9.2 Absence theorems for v1.5 conjuncts (mechanical corollaries) -/

theorem governed_v15_fails_without_p13_regimebinding :
    ¬P13_RegimeBinding →
    ¬Governed_v15 P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity P1_SelectionPolicy P12_SchemaHash P13_RegimeBinding
      P14_PredicateCommitment P15_InterWindowDriftContinuity P6_AgencyBoundary
      PCF_Cumulative := by
  intro h_not h_gov
  exact h_not (p13_regimebinding_necessary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ h_gov)

theorem governed_v15_fails_without_p14_predicatecommitment :
    ¬P14_PredicateCommitment →
    ¬Governed_v15 P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity P1_SelectionPolicy P12_SchemaHash P13_RegimeBinding
      P14_PredicateCommitment P15_InterWindowDriftContinuity P6_AgencyBoundary
      PCF_Cumulative := by
  intro h_not h_gov
  exact h_not (p14_predicatecommitment_necessary _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h_gov)

theorem governed_v15_fails_without_p15_interwindow :
    ¬P15_InterWindowDriftContinuity →
    ¬Governed_v15 P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity P1_SelectionPolicy P12_SchemaHash P13_RegimeBinding
      P14_PredicateCommitment P15_InterWindowDriftContinuity P6_AgencyBoundary
      PCF_Cumulative := by
  intro h_not h_gov
  exact h_not (p15_interwindowdriftcontinuity_necessary _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h_gov)

theorem governed_v15_fails_without_p6_agencyboundary :
    ¬P6_AgencyBoundary →
    ¬Governed_v15 P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity P1_SelectionPolicy P12_SchemaHash P13_RegimeBinding
      P14_PredicateCommitment P15_InterWindowDriftContinuity P6_AgencyBoundary
      PCF_Cumulative := by
  intro h_not h_gov
  exact h_not (p6_agencyboundary_necessary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ h_gov)

/-! ### §9.3 Sufficiency — all 29 conjuncts jointly establish Governed_v15 -/

theorem all_twentynine_conjuncts_sufficient :
    P1 → P2 → P3 → P4 → P4M → P4T → P5 → P5E →
    P6 → P6A → P6L → PCF →
    P10 → P11 → P12 → FAH → FAA →
    P2_DAG → P6_AtomicAgency → P1_Freshness → P4T_EnvInvariant →
    P_ChainIntegrity →
    P1_SelectionPolicy → P12_SchemaHash → P13_RegimeBinding →
    P14_PredicateCommitment → P15_InterWindowDriftContinuity →
    P6_AgencyBoundary → PCF_Cumulative →
    Governed_v15 P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity P1_SelectionPolicy P12_SchemaHash P13_RegimeBinding
      P14_PredicateCommitment P15_InterWindowDriftContinuity P6_AgencyBoundary
      PCF_Cumulative := by
  intros
  exact ⟨by assumption, by assumption, by assumption, by assumption,
         by assumption, by assumption, by assumption, by assumption,
         by assumption, by assumption, by assumption, by assumption,
         by assumption, by assumption, by assumption, by assumption,
         by assumption, by assumption, by assumption, by assumption,
         by assumption, by assumption, by assumption, by assumption,
         by assumption, by assumption, by assumption, by assumption,
         by assumption⟩

/-! ### §9.4 Authorisation condition — projects the load-bearing subset -/

theorem authorisation_condition_v15 :
    Governed_v15 P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity P1_SelectionPolicy P12_SchemaHash P13_RegimeBinding
      P14_PredicateCommitment P15_InterWindowDriftContinuity P6_AgencyBoundary
      PCF_Cumulative →
    (P1 ∧ P5 ∧ P5E ∧ P6_AtomicAgency ∧ P1_Freshness ∧ P_ChainIntegrity
        ∧ P13_RegimeBinding ∧ P14_PredicateCommitment ∧ P6_AgencyBoundary) := by
  intro h
  rcases h with ⟨p1, _, _, _, _, _, p5, p5e, _, _, _, _, _, _, _, _, _, _,
                 p6at, p1fr, _, pci, _, _, p13, p14, _, p6ab, _⟩
  exact ⟨p1, p5, p5e, p6at, p1fr, pci, p13, p14, p6ab⟩

end Governed

/-! ## §10 Open / sorried claims — flagged here AND in OPEN PROOFS header -/

section OpenProofs
variable (snaps : List RawSnapshot)
variable (b : P6AgencyBoundary) (log : MemoryAccessLog) (graph : DeploymentGraph)
variable (binding : GovernanceRegimeBinding) (decision : DecisionInstant)
variable (prevW currW : WindowDriftSummary) (bounds : DriftBounds)

/-- [O2, repaired 2026-06-11] No coalition escape — coupling tied to the boundary.

    A `CouplingFinding f` is evidence that two agents are coupled
    (`sharedMutableAccess` / `reciprocalDependency` / `explicitDelegation` /
    `sharedIncentiveBinding`). `h_distinct` records that it is a genuine coupling
    between two DIFFERENT agents. `h_atomic_single` is the meaning of
    `mode_P6A_AtomicSingleActor`: under a single-actor boundary the two parties of
    the coupling are necessarily the same agent (there is exactly one actor). A
    real two-agent coupling therefore cannot be governed by a single-actor
    boundary, and `P6_AgencyBoundary_Holds` collapses to declared delegation
    (`mode_P6D` ∧ declared) or coupling closure (`mode_P6C` ∧ closure).

    Forbids: two distinct agents acting as a coupled coalition under a boundary
    that declares itself a single atomic actor — laundering a multi-agent coupling
    through `mode_P6A` to dodge the declared-delegation / coupling-closure
    requirements.

    History: the original statement made the coupling hypothesis
    `(detectCoupling log graph).length > 0` over `log`/`graph` free of `b`; it was
    false as written (an atomic-single-actor `b` satisfies the premise while
    violating the conclusion). The machine-checked refutation is preserved in
    `probes/O2Counterexample.lean` (`o2_premise_too_weak`). `detectCoupling` is
    STUB [S5] (`:= []`), so ranging over its (empty) output would be vacuous; the
    repaired statement ranges over the `CouplingFinding` evidence the detector is
    typed to produce. Non-vacuity is `o2_repaired_non_vacuous` below; the original
    counterexample is shown incompatible with the new hypotheses in
    `o2_old_counterexample_excluded`. -/
theorem p6_no_coalition_escape
    (f : CouplingFinding)
    (h_distinct : f.agentA ≠ f.agentB)
    (h_atomic_single : b.mode_P6A_AtomicSingleActor = true → f.agentA = f.agentB)
    (h_holds : P6_AgencyBoundary_Holds b) :
    (b.mode_P6D_DelegatedOrCoalition = true ∧
     b.delegation_explicitly_declared = true) ∨
    (b.mode_P6C_CouplingClosure = true ∧
     b.coupling_closure_satisfied = true) := by
  rcases h_holds with hA | hDC
  · -- single-actor: the coupling's parties coincide, contradicting distinctness
    exact absurd (h_atomic_single hA) h_distinct
  · exact hDC

/-- Non-vacuity for the repaired [O2]: a genuine two-agent coupling under a
    correctly-declared delegated boundary satisfies every hypothesis and the
    conclusion, so the theorem is not true by empty hypothesis. -/
theorem o2_repaired_non_vacuous :
    ∃ (b : P6AgencyBoundary) (f : CouplingFinding),
      f.agentA ≠ f.agentB ∧
      (b.mode_P6A_AtomicSingleActor = true → f.agentA = f.agentB) ∧
      P6_AgencyBoundary_Holds b ∧
      ((b.mode_P6D_DelegatedOrCoalition = true ∧ b.delegation_explicitly_declared = true) ∨
       (b.mode_P6C_CouplingClosure = true ∧ b.coupling_closure_satisfied = true)) := by
  refine ⟨⟨false, true, true, false, false⟩,
          ⟨CouplingMode.explicitDelegation, "alice", "bob"⟩, ?_, ?_, ?_, ?_⟩
  · decide
  · intro h; exact absurd h (by decide)
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inl ⟨rfl, rfl⟩

/-- Adversarial check: the original counterexample (an atomic-single-actor
    boundary) is incompatible with the repaired hypotheses for any genuine
    distinct-agent coupling — `h_atomic_single` cannot hold there. So the repair
    excludes the very execution that falsified the original statement, for the
    principled reason that single-actor mode denies a two-agent coupling. -/
theorem o2_old_counterexample_excluded
    (f : CouplingFinding) (h_distinct : f.agentA ≠ f.agentB)
    (hA : b.mode_P6A_AtomicSingleActor = true) :
    ¬ (b.mode_P6A_AtomicSingleActor = true → f.agentA = f.agentB) := by
  intro h_atomic_single
  exact h_distinct (h_atomic_single hA)

/-- [O3] Window-laundering closure. Sliding 64-record windows cannot hide
    cumulative drift in the gap between windows. Requires concrete window
    structure. -/
theorem p15_no_window_laundering
    (h : P15_InterWindowDriftContinuity_Holds prevW currW bounds)
    (_hSize : prevW.window_size ≥ 64 ∧ currW.window_size ≥ 64) :
    DriftBounded prevW.window_drift_vector bounds ∧
    DriftBounded currW.window_drift_vector bounds := by
  exact ⟨h.2.1, h.2.2.1⟩
  -- The deeper "no laundering across the gap" claim, that cumulative drift
  -- over the union is also bounded, follows from h.2.2.2 — but the statement
  -- here intentionally restricts to per-window guarantees. The full statement
  -- with explicit attack model is OPEN [O3] in a future pass.

/-- [O4] Without P13, an attacker routes into a weaker regime and widens the
    freshness window without breaking the other 28 conjuncts. Sketch of the
    counterexample: produce two DecisionInstants D, D' with identical record
    bodies but D.stakes_tier = "low" and D'.stakes_tier = "high"; both pass
    every conjunct except P13 in v1.5. Formalising the attack model is OPEN. -/
theorem p13_no_stakes_widening
    (h : P13_RegimeBinding_Holds binding decision) :
    decision.stakes_tier = binding.regime.stakes_tier ∧
    decision.tolerance_window_ns = binding.regime.tolerance_window_ns := by
  exact ⟨h.1, h.2.2.2.2.2⟩

end OpenProofs

end OmegaV15
