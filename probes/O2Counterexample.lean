/-
  O2Counterexample.lean — machine-checked evidence that OmegaV15's
  `p6_no_coalition_escape` [O2] is NOT provable from its stated hypotheses.

  The theorem concludes  (P6D ∧ declared) ∨ (P6C ∧ closure)  from
  `P6_AgencyBoundary_Holds b`, but that predicate ALSO admits the
  `mode_P6A` (atomic single actor) disjunct, and the only other
  hypothesis `h : (detectCoupling log graph).length > 0` is about the
  independent variables `log`/`graph`, with no stated link to `b`.

  Below we exhibit a concrete `b` (atomic single actor) that satisfies
  `P6_AgencyBoundary_Holds b` yet falsifies the conclusion. So `h_b`
  cannot entail the conclusion; the obligation is unprovable as written
  until a schema invariant ties `detectCoupling log graph` to `¬ b.mode_P6A`.

  Definitions below are copied VERBATIM from OmegaV15.lean (struct lines
  378-383, predicate lines 385-390) because OmegaV15 is not a Lake module
  and cannot be `import`ed. The original statement is NOT edited (sprint rule).
  Verified via `lake env lean scratch/O2Counterexample.lean`.
-/

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

/-- The premise `P6_AgencyBoundary_Holds b` is strictly too weak to entail the
    `p6_no_coalition_escape` conclusion: an atomic-single-actor boundary
    satisfies the premise while falsifying the conclusion. -/
theorem o2_premise_too_weak :
    ∃ b : P6AgencyBoundary,
      P6_AgencyBoundary_Holds b ∧
      ¬ ((b.mode_P6D_DelegatedOrCoalition = true ∧
          b.delegation_explicitly_declared = true) ∨
         (b.mode_P6C_CouplingClosure = true ∧
          b.coupling_closure_satisfied = true)) := by
  refine ⟨⟨true, false, false, false, false⟩, ?_, ?_⟩
  · exact Or.inl rfl          -- P6_AgencyBoundary_Holds via the mode_P6A disjunct
  · decide                    -- conclusion false: both disjuncts require `false = true`

#print axioms o2_premise_too_weak
