/-
═══════════════════════════════════════════════════════════════════════════
OMEGA — P6A (Aggregate Materiality) SEMANTIC BINDING
═══════════════════════════════════════════════════════════════════════════

PURPOSE. Give ONE conjunct of the shipped 22-way `OmegaV14.Governed` bundle real
verified semantic content, without touching the bundle's structural proofs. The
target is P6A ("Aggregate Materiality"): in `OmegaV14.lean` it is an uninterpreted
`variable (P6A : Prop)` — proved necessary and jointly sufficient in the bundle's
skeleton, but standing for nothing.

P6A's property TYPE is an aggregate-over-a-delegation-tree: "before delegating, the
orchestrating agent must produce a consolidated prediction covering the AGGREGATE
outcome of the entire delegated workflow; individual (per-path) compliance does not
imply aggregate compliance." That is exactly the authority-fork shape proved
axiom-free in CrossLayer/ForkWitness.lean (per-path checks all pass, two siblings
each draw the full grant, the sibling SUM exceeds the root grant, and a tree-level
meter on the aggregate removes the witness). So the paradigm-appropriate backing is
LEAN (kernel, axiom-free) — not a new tool. The semantic content already exists;
this file BINDS it to the P6A atom.

WHAT THIS FILE DOES.
  (1) Inlines the kernel-checked aggregate-meter core from CrossLayer/ForkWitness.lean
      (self-contained re-derivation: core-Lean only, everything reduces to rfl/decide;
      re-checked by the kernel here, byte-traceable to the source file). It defines a
      concrete delegation fork, proves per-path compliance does NOT bound the
      cross-sibling aggregate, and proves a tree-level meter decides it.
  (2) Packages that semantic content as a concrete predicate `P6A_Concrete` and proves
      it (`p6a_concrete_holds`).
  (3) BINDS it to the shipped bundle: instantiates `OmegaV14.Governed` at
      `P6A := P6A_Concrete`, so the P6A slot is discharged by a kernel proof rather
      than assumed (`governed_p6a_instantiated`), and recovers the concrete property
      back out of the bundle (`p6a_concrete_necessary`).

TRUST BASE.  Lean kernel, v4.27.0, ZERO user axioms, propext-free (confirmed by the
`#print axioms` block at the foot of this file). The result holds at the MODEL level:
it establishes that the aggregate-over-delegation property holds in this model and
that P6A can stand for it. It does NOT claim any deployed delegation system matches
the model — same model-vs-deployment boundary as the conserved-meter work.

SCOPE / HONESTY.  Exactly ONE conjunct (P6A) gains verified semantic content here.
The other 21 atoms of `OmegaV14.Governed` remain uninterpreted Props. This is NOT a
claim that "OMEGA is semantically verified" — it is a single, honest, additive
binding, offered as the PATTERN for paradigm-appropriate strengthening.

ADDITIVE.  No shipped file is modified. This module is NOT a Lake root (not in
lakefile.lean); it is checked with `lake env lean OmegaP6ABinding.lean`, the same way
the probes under `probes/` are checked. It imports the real shipped `OmegaV14`.
-/

import OmegaV14

namespace OmegaP6ABinding

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 1 — the aggregate-over-delegation-tree core
-- (kernel-checked re-derivation of CrossLayer/ForkWitness.lean; core-Lean only)
-- ═══════════════════════════════════════════════════════════════════════════

/-- One delegation path: the authority `bound` granted to it, and the `draw` it made. -/
structure Path where
  bound : Nat
  draw  : Nat
  deriving DecidableEq, Repr

/-- A fork of delegation paths sharing one parent authority. -/
abbrev Fork := List Path

/-- The root authority (the budget the human granted at the top of the fork). -/
def grant : Nat := 10

/-- The per-path local check: the path attenuates (its bound is within the root
    grant) and its draw is within its own bound. Reads only this path, no sibling. -/
def localOK (p : Path) : Bool := Nat.ble p.bound grant && Nat.ble p.draw p.bound

/-- Weak observation: the list of per-path local verdicts. Hand-rolled recursion so
    it reduces under `rfl`. Carries no aggregate. -/
def locals : Fork → List Bool
  | []        => []
  | p :: rest => localOK p :: locals rest

/-- Every path passes its own local check (no `List.all`). -/
def allTrue : List Bool → Bool
  | []        => true
  | b :: rest => b && allTrue rest

/-- Weak relation: every per-path local check passes. -/
def ConsLocal (os : List Bool) : Prop := allTrue os = true

/-- The aggregate the per-path relation omits: the sum of sibling draws. -/
def sumDraws : Fork → Nat
  | []        => 0
  | p :: rest => p.draw + sumDraws rest

/-- Security objective / forbidden behaviour: the realised authority (sibling sum)
    exceeds the root grant. Reducible so `decide` sees through it. -/
@[reducible] def FViolates (f : Fork) : Prop := Nat.blt grant (sumDraws f) = true

/-- The authority-fork witness: two paths, each granted the full budget
    (`bound = grant`, faithful re-grant, no amplification) and each drawing it in
    full. Each path attenuates and obeys its own bound, so each per-path check passes. -/
def witnessFork : Fork := [⟨grant, grant⟩, ⟨grant, grant⟩]

/-- The benign partner: same two paths, same per-path verdicts, but the second draws
    nothing — so the sibling sum stays within the grant. -/
def benignFork : Fork := [⟨grant, grant⟩, ⟨grant, 0⟩]

/-- The added observation: the tree-level aggregate meter (sibling sum). -/
def gMeter (f : Fork) : Nat := sumDraws f

/-- The decision predicate of the meter: the aggregate exceeds the grant. -/
@[reducible] def decM (_ : List Bool) (s : Nat) : Prop := Nat.blt grant s = true

/-- The repaired relation: the weak per-path relation, refined by also rejecting the
    metered (aggregate) violations. -/
def ConsRepaired (Cons : List Bool → Prop) (decV : List Bool → Nat → Prop) :
    List Bool → Nat → Prop :=
  fun o v => Cons o ∧ ¬ decV o v

/-- THE HEART OF P6A: per-path compliance does NOT bound the cross-sibling aggregate.
    Every path passes its own local check, yet the realised authority (sibling sum)
    exceeds the root grant. "Individual compliance does not imply aggregate
    compliance," made concrete and kernel-checked. -/
theorem per_path_local_insufficient :
    allTrue (locals witnessFork) = true ∧ FViolates witnessFork :=
  ⟨rfl, rfl⟩

/-- THE REPAIR: a tree-level meter on the aggregate DECIDES the objective and removes
    every authority-fork witness. (`decM` on the metered aggregate is definitionally
    `FViolates`, so a relation that rejects the metered violation rejects the
    violation.) This is the "consolidated prediction covering the aggregate outcome"
    that P6A requires before delegating. -/
theorem tree_meter_removes_witness :
    ∀ f, ConsRepaired ConsLocal decM (locals f) (gMeter f) → ¬ FViolates f := by
  intro f hC hV
  exact hC.2 hV

/-- The repair is not vacuous: the metered relation still accepts the within-grant
    benign fork. Aggregate metering rejects the over-draw without rejecting safe
    delegation. -/
theorem tree_meter_not_vacuous :
    ConsRepaired ConsLocal decM (locals benignFork) (gMeter benignFork) :=
  ⟨rfl, by decide⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 2 — the concrete predicate that P6A stands for
-- ═══════════════════════════════════════════════════════════════════════════

/-- The SEMANTIC CONTENT of P6A (Aggregate Materiality), as a concrete predicate over
    a delegation tree. It asserts three things together:

      (1) per-path compliance does NOT bound the cross-sibling aggregate
          (a fork where every per-path check passes yet the aggregate breaches the
          root grant) — i.e. individual compliance does not imply aggregate
          compliance;

      (2) a tree-level aggregate meter ("consolidated prediction covering the
          aggregate outcome") DECIDES the objective and removes every such witness;

      (3) that meter is not vacuous — it still accepts safe (within-grant) delegation.

    This is what an honest P6A demands of an orchestrating agent before it delegates. -/
def P6A_Concrete : Prop :=
  (allTrue (locals witnessFork) = true ∧ FViolates witnessFork)
  ∧ (∀ f, ConsRepaired ConsLocal decM (locals f) (gMeter f) → ¬ FViolates f)
  ∧ ConsRepaired ConsLocal decM (locals benignFork) (gMeter benignFork)

/-- `P6A_Concrete` HOLDS — kernel-checked, axiom-free. P6A is no longer an empty atom:
    here is a verified property it stands for. -/
theorem p6a_concrete_holds : P6A_Concrete :=
  ⟨per_path_local_insufficient, tree_meter_removes_witness, tree_meter_not_vacuous⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 3 — the binding to the shipped bundle (OmegaV14.Governed)
-- ═══════════════════════════════════════════════════════════════════════════
--
-- `OmegaV14.Governed` is parametric in the 22 atoms (each a `Prop` variable). The
-- binding shows the P6A slot can be INSTANTIATED by the concrete, verified
-- `P6A_Concrete`: the bundle still composes, and because `P6A_Concrete` is proven,
-- the P6A slot is DISCHARGED by a kernel proof rather than assumed — unlike the
-- other 21 atoms, which remain hypotheses.

/-- SUFFICIENCY, with P6A made concrete. To establish `Governed` with the P6A slot
    set to `P6A_Concrete` we need ONLY the other 21 atoms as hypotheses — the P6A
    obligation is met by `p6a_concrete_holds`. This is the binding: the abstract P6A
    atom is replaced by a concrete, kernel-verified property and the bundle still
    holds. -/
theorem governed_p6a_instantiated
    (P1 P2 P3 P4 P4M P4T P5 P5E P6 P6L PCF : Prop)
    (P10 P11 P12 FAH FAA : Prop)
    (P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity : Prop)
    (p1 : P1) (p2 : P2) (p3 : P3) (p4 : P4) (p4m : P4M) (p4t : P4T)
    (p5 : P5) (p5e : P5E) (p6 : P6) (p6l : P6L) (pcf : PCF)
    (p10 : P10) (p11 : P11) (p12 : P12) (fah : FAH) (faa : FAA)
    (p2dag : P2_DAG) (p6atom : P6_AtomicAgency) (p1fr : P1_Freshness)
    (p4tenv : P4T_EnvInvariant) (pchain : P_ChainIntegrity) :
    OmegaV14.Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A_Concrete P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity :=
  OmegaV14.all_twentytwo_conjuncts_sufficient
    P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A_Concrete P6L PCF
    P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
    P_ChainIntegrity
    p1 p2 p3 p4 p4m p4t p5 p5e p6 p6a_concrete_holds p6l pcf
    p10 p11 p12 fah faa p2dag p6atom p1fr p4tenv pchain

/-- NECESSITY, recovered at the concrete instance. The P6A slot of the shipped bundle,
    once instantiated to `P6A_Concrete`, yields the concrete aggregate-materiality
    property back out — so the binding is faithful in both directions: the bundle does
    not merely tolerate the concrete P6A, it carries it. (P6A is the 10th conjunct;
    this is the same projection the bundle's own necessity lemmas use.) -/
theorem p6a_concrete_necessary
    (P1 P2 P3 P4 P4M P4T P5 P5E P6 P6L PCF : Prop)
    (P10 P11 P12 FAH FAA : Prop)
    (P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant P_ChainIntegrity : Prop) :
    OmegaV14.Governed P1 P2 P3 P4 P4M P4T P5 P5E P6 P6A_Concrete P6L PCF
      P10 P11 P12 FAH FAA P2_DAG P6_AtomicAgency P1_Freshness P4T_EnvInvariant
      P_ChainIntegrity
    → P6A_Concrete :=
  fun h => h.2.2.2.2.2.2.2.2.2.1

-- ═══════════════════════════════════════════════════════════════════════════
-- AXIOM AUDIT — trust base is the Lean kernel, zero user axioms, propext-free.
-- ═══════════════════════════════════════════════════════════════════════════

#print axioms per_path_local_insufficient
#print axioms tree_meter_removes_witness
#print axioms tree_meter_not_vacuous
#print axioms p6a_concrete_holds
#print axioms governed_p6a_instantiated
#print axioms p6a_concrete_necessary

end OmegaP6ABinding
