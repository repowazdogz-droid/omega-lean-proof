/-
═══════════════════════════════════════════════════════════════════════════════
  OmegaP5Gate.lean — Lean 4 model of the P5 gate evaluator `f`.
═══════════════════════════════════════════════════════════════════════════════

  Mirrors omega-contracts/src/gate-evaluator.ts (the R1–R22 ordered rule list).
  Self-contained: no imports, no Mathlib, no custom axioms, zero `sorry`. NOT a
  Lake-root sibling of OmegaV15 (whose open `sorry` stays quarantined); this is
  its own root.

  ─────────────────────────────────────────────────────────────────────────────
  HONEST SCOPE (PRIMITIVE_MAP register) — what `f` proves and does NOT prove
  ─────────────────────────────────────────────────────────────────────────────
  `f` proves that `gate_result` is the deterministic output of a declared,
  published function over fields already in the record. A verifier can recompute
  `f(inputs)` and confirm it equals the recorded `gate_result`. It does NOT prove
  the recorded inputs were true, does NOT prove this policy is the correct or
  mandated policy, and does NOT prove a human actually performed any escalation
  `f` demands. A cleared escalation proves "an identified party, distinct from
  the acting actor, recorded a cryptographically-bound approval scoped to
  specific triggers over this record's evidence digest" — it does NOT prove that
  party was authorised, competent, or honest (FAA-class limit, Attestation
  Authority Integrity), the same trust hole as the unsigned actor_id.
  Hard-blocked conditions (R3, R4, R5) are non-overridable by design.

  G4 (cryptographic attestation of oversight) is modelled here as the abstract
  predicate `oversightAttested`, instantiated FAIL-CLOSED (`:= false`) until the
  signature layer (build step 3) ships. The rule SHAPE is final, so swapping in
  the real verifier needs no change to `f`'s precedence or these theorems.
═══════════════════════════════════════════════════════════════════════════════
-/

namespace OmegaP5Gate

/-! ## §1 Result, stakes, evidence enums -/

inductive GateResult
  | committed | held | escalated
  deriving DecidableEq

inductive Stakes
  | low | moderate | high | critical

inductive HarmLabel
  | negligible | minor | moderate | severe | critical | catastrophic

inductive AssumptionGateState
  | pass | caution | block

inductive Disposition
  | approved | rejected

/-! ## §2 Evidence slot models (counts as `Nat`, presence as `Option`) -/

structure Assumption where
  loadBearingCount     : Nat
  loadBearingValidated : Nat
  gate                 : AssumptionGateState

structure Consent where
  violations    : Nat
  critical      : Nat
  major         : Nat
  scopeCreep    : Bool
  chainVerified : Bool

structure Ethics where
  requiresHumanReview : Nat
  flagCritical        : Nat
  flagMajor           : Nat
  unackFlags          : Nat
  weaponisation       : Nat

structure Harm where
  /-- `none` = severity unknown (recorded label was null). -/
  label : Option HarmLabel

structure Trust where
  /-- overall_availability = available AND overall_score ≠ null. -/
  available       : Bool
  /-- overall_score < TRUST_FLOOR (meaningful only when `available`). -/
  scoreBelowFloor : Bool

structure Clearpath where
  verificationFailures : Nat

structure Oversight where
  disposition : Disposition
  g1          : Bool          -- separation of duties (approver ≠ actor)
  cleared     : List String   -- cleared_triggers
  g3          : Bool          -- anti-transplant digest match

structure GateInput where
  stakes     : Stakes
  blockedBy  : Bool
  assumption : Option Assumption
  consent    : Option Consent
  ethics     : Option Ethics
  harm       : Option Harm
  trust      : Option Trust
  clearpath  : Option Clearpath
  oversight  : Option Oversight

/-! ## §3 Stakes predicates -/

def Stakes.isCritical : Stakes → Bool | .critical => true | _ => false
def Stakes.isHigh     : Stakes → Bool | .high => true | _ => false
def Stakes.elevated   : Stakes → Bool | .high => true | .critical => true | _ => false
def Stakes.nontrivial : Stakes → Bool
  | .moderate => true | .high => true | .critical => true | _ => false

/-! ## §4 Oversight clearing — G1, G2, G3 live; G4 fail-closed -/

/-- G4. Cryptographic attestation. FAIL-CLOSED until build step 3. -/
def oversightAttested (_ : Oversight) : Bool := false

/-- `clears ov? t`: oversight clears trigger `t` only if disposition = approved
    AND all four guards hold. Only the clearable rules {R1,R2,R6,R7} consult it. -/
def clears (ov? : Option Oversight) (t : String) : Bool :=
  match ov? with
  | none => false
  | some ov =>
      (match ov.disposition with | .approved => true | .rejected => false)
        && ov.g1 && ov.cleared.contains t && ov.g3 && oversightAttested ov

/-! ## §5 Evidence accessors (slot-absent → 0/false) -/

def pos (n : Nat) : Bool := decide (0 < n)

def ethRHR (i : GateInput) : Nat := match i.ethics with | some e => e.requiresHumanReview | none => 0
def ethFC  (i : GateInput) : Nat := match i.ethics with | some e => e.flagCritical | none => 0
def ethWP  (i : GateInput) : Nat := match i.ethics with | some e => e.weaponisation | none => 0
def ethFM  (i : GateInput) : Nat := match i.ethics with | some e => e.flagMajor | none => 0
def ethUA  (i : GateInput) : Nat := match i.ethics with | some e => e.unackFlags | none => 0
def conCR  (i : GateInput) : Nat := match i.consent with | some c => c.critical | none => 0
def conMJ  (i : GateInput) : Nat := match i.consent with | some c => c.major | none => 0
def conVI  (i : GateInput) : Nat := match i.consent with | some c => c.violations | none => 0

def harmCritPlus (i : GateInput) : Bool :=
  match i.harm with
  | some h => match h.label with | some .critical => true | some .catastrophic => true | _ => false
  | none => false

def harmSevere (i : GateInput) : Bool :=
  match i.harm with
  | some h => match h.label with | some .severe => true | _ => false
  | none => false

def harmUnknown (i : GateInput) : Bool :=
  match i.harm with | some h => h.label.isNone | none => false

/-! ## §6 The R1–R21 firing conditions (oversight guards baked into R1,R2,R6,R7) -/

def r1  (i : GateInput) : Bool := i.blockedBy && !(clears i.oversight "R1")
def r2  (i : GateInput) : Bool := pos (ethRHR i) && !(clears i.oversight "R2")
def r3  (i : GateInput) : Bool := pos (ethFC i) || pos (ethWP i)
def r4  (i : GateInput) : Bool := harmCritPlus i
def r5  (i : GateInput) : Bool := pos (conCR i)
def r6  (i : GateInput) : Bool :=
  match i.assumption with
  | some a => i.stakes.isCritical && decide (a.loadBearingValidated < a.loadBearingCount)
              && !(clears i.oversight "R6")
  | none => false
def r7  (i : GateInput) : Bool :=
  match i.assumption with
  | none   => i.stakes.isCritical && !(clears i.oversight "R7")
  | some _ => false
def r8  (i : GateInput) : Bool :=
  match i.clearpath with | some c => pos c.verificationFailures | none => false
def r9  (i : GateInput) : Bool :=
  match i.assumption with | some a => (match a.gate with | .block => true | _ => false) | none => false
def r10 (i : GateInput) : Bool :=
  match i.consent with | some c => !c.chainVerified | none => false
def r11 (i : GateInput) : Bool := pos (conMJ i)
def r12 (i : GateInput) : Bool := pos (ethFM i) || pos (ethUA i)
def r13 (i : GateInput) : Bool := harmSevere i
def r14 (i : GateInput) : Bool := harmUnknown i && i.stakes.nontrivial
def r15 (i : GateInput) : Bool :=
  match i.assumption with
  | some a => i.stakes.isHigh && decide (a.loadBearingValidated < a.loadBearingCount)
  | none => false
def r16 (i : GateInput) : Bool :=
  match i.assumption with
  | some a => (match a.gate with | .caution => true | _ => false) && i.stakes.elevated
  | none => false
def r17 (i : GateInput) : Bool :=
  match i.trust with | some t => i.stakes.elevated && t.available && t.scoreBelowFloor | none => false
def r18 (i : GateInput) : Bool :=
  match i.trust with | some t => i.stakes.isCritical && !t.available | none => false
def r19 (i : GateInput) : Bool :=
  i.stakes.elevated && (i.consent.isNone || i.ethics.isNone || i.harm.isNone)
def r20 (i : GateInput) : Bool :=
  match i.consent with | some c => c.scopeCreep && i.stakes.elevated | none => false
def r21 (i : GateInput) : Bool :=
  match i.consent with | some c => pos c.violations && i.stakes.isCritical | none => false

/-! ## §7 `f` — ordered, first-match-wins -/

/-- The ordered rule list: `(firing-condition, result)` pairs in R1…R21 order.
    R1–R7 escalate, R8–R21 hold. The R22 default is the `foldr` seed below. This
    is the faithful encoding of the first-match-wins precedence and equals the
    nested `if`-chain definitionally. -/
def ruleList (i : GateInput) : List (Bool × GateResult) :=
  [ (r1 i, .escalated),  (r2 i, .escalated),  (r3 i, .escalated),  (r4 i, .escalated),
    (r5 i, .escalated),  (r6 i, .escalated),  (r7 i, .escalated),
    (r8 i, .held),  (r9 i, .held),  (r10 i, .held), (r11 i, .held), (r12 i, .held),
    (r13 i, .held), (r14 i, .held), (r15 i, .held), (r16 i, .held), (r17 i, .held),
    (r18 i, .held), (r19 i, .held), (r20 i, .held), (r21 i, .held) ]

/-- First-match-wins fold: returns the result of the first firing rule, else the
    R22 default `.committed`. -/
def f (i : GateInput) : GateResult :=
  (ruleList i).foldr (fun rule acc => if rule.1 then rule.2 else acc) .committed

/-- Some R1–R21 rule fires (the negation of "reaches R22"). -/
def anyRuleFires (i : GateInput) : Bool :=
  (ruleList i).any (·.1)

/-! ## §8 Theorems (kernel-checked, zero sorry) -/

/-- `f` is total and single-valued: it returns exactly one of the three results. -/
theorem gate_total (i : GateInput) :
    f i = .committed ∨ f i = .held ∨ f i = .escalated := by
  cases h : f i with
  | committed => exact Or.inl rfl
  | held      => exact Or.inr (Or.inl rfl)
  | escalated => exact Or.inr (Or.inr rfl)

/-- Determinism: any recorded result consistent with `f` is unique (because `f`
    is a function — there is no second admissible `gate_result`). -/
theorem gate_deterministic (i : GateInput) (x y : GateResult)
    (hx : x = f i) (hy : y = f i) : x = y := by
  rw [hx, hy]

/-- A benign record (no triggers) evaluates to COMMITTED — `f` is not vacuous. -/
def benign : GateInput :=
  { stakes := .low, blockedBy := false, assumption := none, consent := none,
    ethics := none, harm := none, trust := none, clearpath := none, oversight := none }

theorem non_vacuity : f benign = .committed := by decide

/-! ### General `foldr` lemmas (O(n) induction — no giant if-terms) -/

private def gateStep (rule : Bool × GateResult) (acc : GateResult) : GateResult :=
  if rule.1 then rule.2 else acc

/-- If some rule fires and every rule's result is ≠ COMMITTED, the fold is
    ≠ COMMITTED (COMMITTED can only be the untouched seed). -/
theorem foldr_ne_committed :
    ∀ (L : List (Bool × GateResult)) (init : GateResult),
      (∀ x ∈ L, x.2 ≠ GateResult.committed) → L.any (·.1) = true →
      L.foldr gateStep init ≠ GateResult.committed := by
  intro L
  induction L with
  | nil => intro init _ hany; simp at hany
  | cons hd tl ih =>
    intro init hres hany
    cases hc : hd.1 with
    | false =>
      have htl : tl.any (·.1) = true := by
        simp only [List.any_cons, hc, Bool.false_or] at hany; exact hany
      have hres' : ∀ x ∈ tl, x.2 ≠ GateResult.committed :=
        fun x hx => hres x (List.mem_cons_of_mem _ hx)
      simpa [List.foldr_cons, gateStep, hc] using ih init hres' htl
    | true =>
      have hne : hd.2 ≠ GateResult.committed := hres hd (List.mem_cons_self ..)
      simpa [List.foldr_cons, gateStep, hc] using hne

/-- If every rule in a prefix shares result `v` and some prefix rule fires, the
    fold over `prefix ++ suffix` equals `v` (the first firing rule wins inside
    the constant-result prefix). -/
theorem foldr_const_prefix :
    ∀ (pre suf : List (Bool × GateResult)) (v init : GateResult),
      (∀ x ∈ pre, x.2 = v) → pre.any (·.1) = true →
      (pre ++ suf).foldr gateStep init = v := by
  intro pre
  induction pre with
  | nil => intro suf v init _ hany; simp at hany
  | cons hd tl ih =>
    intro suf v init hpre hany
    cases hc : hd.1 with
    | false =>
      have htl : tl.any (·.1) = true := by
        simp only [List.any_cons, hc, Bool.false_or] at hany; exact hany
      have hpre' : ∀ x ∈ tl, x.2 = v := fun x hx => hpre x (List.mem_cons_of_mem _ hx)
      simpa [List.cons_append, List.foldr_cons, gateStep, hc] using ih suf v init hpre' htl
    | true =>
      have hv : hd.2 = v := hpre hd (List.mem_cons_self ..)
      simp [List.cons_append, List.foldr_cons, gateStep, hc, hv]

/-! ### The gate theorems -/

/-- LOAD-BEARING: no false COMMIT. If any R1–R21 condition fires (with its
    oversight clears having failed, since those are baked into r1/r2/r6/r7),
    `f` is NOT COMMITTED. Conservative blocking holds by construction. -/
theorem no_false_commit (i : GateInput) (h : anyRuleFires i = true) :
    f i ≠ .committed := by
  have hres : ∀ x ∈ ruleList i, x.2 ≠ GateResult.committed := by
    simp only [ruleList, List.forall_mem_cons]
    decide
  exact foldr_ne_committed (ruleList i) .committed hres h

/-- The contrapositive view: COMMITTED is reached only when every rule is quiet. -/
theorem committed_implies_quiet (i : GateInput) (h : f i = .committed) :
    anyRuleFires i = false := by
  cases hb : anyRuleFires i with
  | false => rfl
  | true  => exact absurd h (no_false_commit i hb)

/-- The R1–R7 prefix all share result ESCALATED. -/
private def escPrefix (i : GateInput) : List (Bool × GateResult) :=
  [ (r1 i, .escalated), (r2 i, .escalated), (r3 i, .escalated), (r4 i, .escalated),
    (r5 i, .escalated), (r6 i, .escalated), (r7 i, .escalated) ]

private def heldSuffix (i : GateInput) : List (Bool × GateResult) :=
  [ (r8 i, .held), (r9 i, .held), (r10 i, .held), (r11 i, .held), (r12 i, .held),
    (r13 i, .held), (r14 i, .held), (r15 i, .held), (r16 i, .held), (r17 i, .held),
    (r18 i, .held), (r19 i, .held), (r20 i, .held), (r21 i, .held) ]

/-- Hard blocks are absorbing: any of R3/R4/R5 firing forces ESCALATED (those
    sit inside the all-ESCALATED R1–R7 prefix, so the first firing rule wins
    ESCALATED before any HELD rule or the COMMITTED seed is reached). -/
theorem hard_blocks_absorbing (i : GateInput)
    (h : r3 i = true ∨ r4 i = true ∨ r5 i = true) : f i = .escalated := by
  have hpre : ∀ x ∈ escPrefix i, x.2 = GateResult.escalated := by
    simp [escPrefix]
  have hany : (escPrefix i).any (·.1) = true := by
    simp only [escPrefix, List.any_cons, List.any_nil, Bool.or_false]
    cases h with
    | inl h => simp [h]
    | inr h => cases h with
      | inl h => simp [h]
      | inr h => simp [h]
  show (ruleList i).foldr gateStep .committed = .escalated
  have hsplit : ruleList i = escPrefix i ++ heldSuffix i := rfl
  rw [hsplit]
  exact foldr_const_prefix (escPrefix i) (heldSuffix i) .escalated .committed hpre hany

/-- R3/R4/R5 ignore the oversight slot (definitional). -/
theorem r3_oversight_irrelevant (i : GateInput) (ov : Option Oversight) :
    r3 { i with oversight := ov } = r3 i := rfl
theorem r4_oversight_irrelevant (i : GateInput) (ov : Option Oversight) :
    r4 { i with oversight := ov } = r4 i := rfl
theorem r5_oversight_irrelevant (i : GateInput) (ov : Option Oversight) :
    r5 { i with oversight := ov } = r5 i := rfl

/-- Hard blocks are unclearable: R3/R4/R5 ignore the oversight block entirely, so
    no approval (any `ov`) can move the record off ESCALATED. -/
theorem hard_blocks_unclearable (i : GateInput) (ov : Option Oversight)
    (h : r3 i = true ∨ r4 i = true ∨ r5 i = true) :
    f { i with oversight := ov } = .escalated := by
  apply hard_blocks_absorbing
  rw [r3_oversight_irrelevant, r4_oversight_irrelevant, r5_oversight_irrelevant]
  exact h

/-- A rejected disposition never clears any trigger. -/
theorem rejected_never_clears (ov : Oversight) (t : String)
    (h : ov.disposition = .rejected) : clears (some ov) t = false := by
  simp [clears, h]

/-- Consequence: with a rejected oversight block, the guarded R2 rule still fires
    (when human review was demanded). The escalation is not dischargeable. -/
theorem rejected_keeps_r2 (i : GateInput) (ov : Oversight)
    (hov : i.oversight = some ov) (hrej : ov.disposition = .rejected)
    (hr : 0 < ethRHR i) : r2 i = true := by
  unfold r2 pos
  rw [hov, rejected_never_clears ov "R2" hrej]
  simp [hr]

/-- FAIL-CLOSED (current shipping truth): with G4 hard-wired false, NOTHING
    clears — every oversight block, for every trigger, yields `false`. -/
theorem failclosed_now (ov? : Option Oversight) (t : String) :
    clears ov? t = false := by
  cases ov? with
  | none => rfl
  | some ov => simp [clears, oversightAttested]

/-! ## §9 Axiom receipts -/

#print axioms gate_total
#print axioms gate_deterministic
#print axioms no_false_commit
#print axioms committed_implies_quiet
#print axioms hard_blocks_absorbing
#print axioms hard_blocks_unclearable
#print axioms rejected_never_clears
#print axioms rejected_keeps_r2
#print axioms failclosed_now
#print axioms non_vacuity

end OmegaP5Gate
