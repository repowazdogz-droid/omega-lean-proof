/-
═══════════════════════════════════════════════════════════════════════════
OMEGA — P2_DAG SEMANTIC BINDING
═══════════════════════════════════════════════════════════════════════════

PURPOSE.  Give the P2_DAG conjunct of the shipped 22-way `OmegaV14.Governed` bundle
real verified semantic content, additively, the same way `OmegaP6ABinding.lean` did
for P6A. In `OmegaV14.lean`, P2_DAG is an uninterpreted `variable (P2_DAG : Prop)` —
"the P2 causal/reasoning graph must be a Directed Acyclic Graph": no node justifies
itself via its own outputs.

PROPERTY TYPE.  Acyclicity / well-foundedness over the justification relation. This
is NOT a pure `rfl`/`decide` fit like P6A/P4T/P6L: showing that a cyclic structure
has NO valid grounding quantifies over all rankings, so it needs a genuine (small,
axiom-free) well-foundedness argument — a strictly-decreasing rank along every
justification edge cannot exist around a cycle. That argument is the semantic core:

  * the blind local check ("every reasoning node cites a justifier") passes for a
    cyclic chain too — it cannot see the cycle;
  * a 2-cycle (node 0 cites 1, node 1 cites 0) is a self-justifying witness;
  * the acyclicity certificate (a rank that strictly decreases along every edge)
    PROVABLY removes every self-justifying witness, and still accepts a genuinely
    grounded chain (non-vacuity).

The witness/non-vacuity reduce by `rfl`/closed-term; the removal theorem
(`grounded_no_cycle`) is the real content and is proved by induction on the
transitive closure using `Nat.lt_trans` / `Nat.lt_irrefl` — all axiom-free.

TRUST BASE.  Lean kernel, v4.27.0, ZERO user axioms (confirmed by `#print axioms`
below). MODEL-LEVEL only: the acyclicity property holds in this model and P2_DAG can
stand for it; NO claim that a deployed reasoning system matches the model.

ADDITIVE.  No shipped file modified. Not a Lake root; checked with
`lake env lean OmegaP2DAGBinding.lean`. Imports the real shipped `OmegaV14`.
-/

import OmegaV14

namespace OmegaP2DAGBinding

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 1 — the justification-graph model
-- ═══════════════════════════════════════════════════════════════════════════

/-- One justification step: a reasoning `node` and the node it cites as its
    justification (`justBy`). -/
structure Step where
  node   : Nat
  justBy : Nat
  deriving DecidableEq, Repr

/-- A reasoning chain: a list of justification steps (the edges of the graph). -/
abbrev Chain := List Step

/-- The blind local check: every step records a cited justifier. True for cyclic and
    grounded chains alike — it cannot see whether the citations form a cycle. -/
def cites (_ : Step) : Bool := true

/-- Every step passes its own local check (no `List.all`). -/
def localAll : Chain → Bool
  | []        => true
  | s :: rest => cites s && localAll rest

/-- Membership of a justification edge `a → b` in the chain, as a Prop inductive
    (kept propositional to stay axiom-free; no Bool algebra). -/
inductive StepIn : Chain → Nat → Nat → Prop
  | head {s rest a b} : s.node = a → s.justBy = b → StepIn (s :: rest) a b
  | tail {s rest a b} : StepIn rest a b → StepIn (s :: rest) a b

/-- Transitive closure (length ≥ 1) of the justification relation: `a` depends,
    through one or more citation steps, on `b`. -/
inductive ReachPlus (c : Chain) : Nat → Nat → Prop
  | base {a b}   : StepIn c a b → ReachPlus c a b
  | step {a b d} : StepIn c a b → ReachPlus c b d → ReachPlus c a d

/-- Self-justification: some node justifies itself through a cycle. -/
def SelfJustifies (c : Chain) : Prop := ∃ a, ReachPlus c a a

/-- The acyclicity certificate (the meter): a rank that strictly decreases along
    every justification edge — justifiers are strictly more basic than what they
    justify. Hand-rolled recursion. -/
def decreasing (rank : Nat → Nat) : Chain → Prop
  | []        => True
  | s :: rest => rank s.justBy < rank s.node ∧ decreasing rank rest

/-- A chain is grounded (a DAG) iff such a strictly-decreasing rank exists. -/
def Grounded (c : Chain) : Prop := ∃ rank : Nat → Nat, decreasing rank c

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 2 — the well-foundedness core (the real semantic content)
-- ═══════════════════════════════════════════════════════════════════════════

/-- A decreasing rank strictly decreases across any single edge present in the chain. -/
theorem decreasing_step {rank : Nat → Nat} {c : Chain} {a b : Nat}
    (hin : StepIn c a b) : decreasing rank c → rank b < rank a := by
  induction hin with
  | head h1 h2 => intro hdec; subst h1; subst h2; exact hdec.1
  | tail _ ih => intro hdec; exact ih hdec.2

/-- A decreasing rank strictly decreases across any reach-path: if `a` reaches `b`,
    then `rank b < rank a`. -/
theorem reach_decreases {rank : Nat → Nat} {c : Chain} {a b : Nat}
    (hdec : decreasing rank c) (hr : ReachPlus c a b) : rank b < rank a := by
  induction hr with
  | base hstep => exact decreasing_step hstep hdec
  | step hstep _ ih => exact Nat.lt_trans ih (decreasing_step hstep hdec)

/-- THE REMOVAL THEOREM: a grounded (acyclic-certified) chain has no self-justifying
    witness. If a strictly-decreasing rank exists, no node can reach itself, because
    that would force `rank a < rank a`. -/
theorem grounded_no_cycle {c : Chain} : Grounded c → ¬ SelfJustifies c := by
  intro hg hsj
  obtain ⟨rank, hdec⟩ := hg
  obtain ⟨a, hreach⟩ := hsj
  exact Nat.lt_irrefl (rank a) (reach_decreases hdec hreach)

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 3 — concrete witness and grounded chain
-- ═══════════════════════════════════════════════════════════════════════════

/-- The self-justification witness: node 0 cites node 1, node 1 cites node 0 — a
    2-cycle. Each step individually cites a justifier (local check passes); the chain
    as a whole is self-justifying. -/
def witnessChain : Chain := [⟨0, 1⟩, ⟨1, 0⟩]

/-- The benign partner: node 1 cites node 0 (a base fact), node 2 cites node 1 — a
    genuinely grounded chain. -/
def benignChain : Chain := [⟨1, 0⟩, ⟨2, 1⟩]

/-- The witness self-justifies: 0 reaches 0 via 0 → 1 → 0. -/
theorem witness_self_justifies : SelfJustifies witnessChain :=
  ⟨0, ReachPlus.step (StepIn.head rfl rfl)
        (ReachPlus.base (StepIn.tail (StepIn.head rfl rfl)))⟩

/-- THE HEART OF P2_DAG: the local "every node cites a justifier" check passes, yet
    the chain self-justifies. Citation-presence does not imply groundedness. -/
theorem cyclic_local_insufficient :
    localAll witnessChain = true ∧ SelfJustifies witnessChain :=
  ⟨rfl, witness_self_justifies⟩

/-- The benign chain is grounded: the identity rank strictly decreases along every
    edge (0 < 1 and 1 < 2). -/
theorem benign_grounded : Grounded benignChain :=
  -- identity rank: 0 < 1 (node 1 cites fact 0) and 1 < 2 (node 2 cites node 1).
  -- `decreasing` is a recursive Prop with no blanket `Decidable` instance, so the
  -- grounding is given as an explicit term (each `<` leaf decided individually)
  -- rather than by `decide` over the whole conjunction.
  ⟨fun n => n, by decide, by decide, trivial⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 4 — the concrete predicate that P2_DAG stands for
-- ═══════════════════════════════════════════════════════════════════════════

/-- The SEMANTIC CONTENT of P2_DAG: (1) citation-presence does not imply groundedness
    — a cyclic chain that passes the local check yet self-justifies; (2) the
    acyclicity certificate removes every self-justifying witness; (3) a genuinely
    grounded chain is still accepted. -/
def P2DAG_Concrete : Prop :=
  (localAll witnessChain = true ∧ SelfJustifies witnessChain)
  ∧ (∀ c, Grounded c → ¬ SelfJustifies c)
  ∧ (localAll benignChain = true ∧ Grounded benignChain)

/-- `P2DAG_Concrete` HOLDS — kernel-checked, axiom-free. -/
theorem p2dag_concrete_holds : P2DAG_Concrete :=
  ⟨cyclic_local_insufficient, fun _ hg => grounded_no_cycle hg, ⟨rfl, benign_grounded⟩⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 5 — the binding to the shipped bundle (slot 18: P2_DAG)
-- ═══════════════════════════════════════════════════════════════════════════

/-- SUFFICIENCY, with P2_DAG made concrete: `Governed` holds with that slot set to
    `P2DAG_Concrete`, discharged by `p2dag_concrete_holds` rather than assumed,
    needing only the other 21 atoms as hypotheses. -/
theorem governed_p2dag_instantiated
    (P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF : Prop)
    (P10 P11 P12 FAH FAA : Prop)
    (P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity : Prop)
    (p1 : P1) (p2 : P2) (p3 : P3) (p4 : P4) (p4m : P4M) (p4t : P4T)
    (p5 : P5) (p5e : P5E) (p6 : P6) (p6a : P6A) (p6l : P6L) (pcf : PCF)
    (p10 : P10) (p11 : P11) (p12 : P12) (fah : FAH) (faa : FAA)
    (p6atom : P6_AtomicAgency) (p1fr : P1_Freshness)
    (p4tenv : P4T_EnvInvariant) (pchain : P_ChainIntegrity) :
    OmegaV14.Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2DAG_Concrete P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity :=
  OmegaV14.all_twentytwo_conjuncts_sufficient
    P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
    P10 P11 P12 FAH FAA P2DAG_Concrete P6_AtomicAgency P1_Freshness P4T_EnvInvariant
    P_ChainIntegrity
    p1 p2 p3 p4 p4m p4t p5 p5e p6 p6a p6l pcf
    p10 p11 p12 fah faa p2dag_concrete_holds p6atom p1fr p4tenv pchain

/-- NECESSITY, recovered at the concrete instance: the bundle instantiated at
    `P2DAG_Concrete` hands the property back out (slot 18, the same projection the
    bundle's own `p2_dag_necessary` uses). -/
theorem p2dag_concrete_necessary
    (P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF : Prop)
    (P10 P11 P12 FAH FAA : Prop)
    (P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity : Prop) :
    OmegaV14.Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A P6L PCF
      P10 P11 P12 FAH FAA P2DAG_Concrete P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity
    → P2DAG_Concrete :=
  fun h => h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

-- ═══════════════════════════════════════════════════════════════════════════
-- AXIOM AUDIT
-- ═══════════════════════════════════════════════════════════════════════════

#print axioms decreasing_step
#print axioms reach_decreases
#print axioms grounded_no_cycle
#print axioms cyclic_local_insufficient
#print axioms benign_grounded
#print axioms p2dag_concrete_holds
#print axioms governed_p2dag_instantiated
#print axioms p2dag_concrete_necessary

end OmegaP2DAGBinding
