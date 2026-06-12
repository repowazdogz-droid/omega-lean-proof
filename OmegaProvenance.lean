/-
═══════════════════════════════════════════════════════════════════════════════
  OmegaProvenance.lean — Lean 4 model of P_VersionProvenance (generation
  provenance: model / prompt binding).
═══════════════════════════════════════════════════════════════════════════════

  Mirrors omega-contracts/src/provenance.ts (`hasVersionProvenance`) and the
  optional `generation` block in omega-record.schema.json. Self-contained: no
  imports, no Mathlib, no custom axioms, zero `sorry`. Its own Lake root, NOT a
  member of the Governed bundle (bundle membership is a v1.5 decision); does not
  touch OmegaV14 / OmegaV15.

  ─────────────────────────────────────────────────────────────────────────────
  HONEST SCOPE — what this proves and does NOT prove
  ─────────────────────────────────────────────────────────────────────────────
  `hasProv` proves only the PRESENCE and WELL-FORMEDNESS of declared generator
  identifiers: a `generation` block exists, `modelId`/`modelVersion` are
  non-empty, and `promptHash` (if present) has the bound digest shape. It does
  NOT prove the declared model actually produced the record, NOT that the
  promptHash commits the real prompt (no preimage is checked here), and NOT that
  the identifiers name a real or honest model. Binding the declared generator to
  the actual generation event is actor-binding / cryptographic attestation (the
  signature layer) — the same trust hole as the unsigned actor_id. Presence +
  shape only; that is why this needs NO crypto axiom (target: zero user axioms).

  PROMPT-HASH SHAPE. The TS/JSON layer carries `prompt_hash` as a 64-char
  lowercase-hex sha256 string; here the same 256-bit digest is modelled as a
  32-element byte digest (`List UInt8`) and well-formedness is the width shape
  (`length = 32`). Same property, byte vs hex encoding. This clones the P14
  PredicateCommitment hash-binding shape (a fixed-width digest field) from
  OmegaV15.

  DIGEST EXCLUSION IS NOT A TRANSPLANT HOLE. `generation` is deliberately kept
  out of the P5 gate's `gate_input_digest` (it is not an input `f` reads). So two
  records identical in subject+evidence but differing only in `generation` share
  a gate_input_digest. An oversight approval still cannot be transplanted between
  them: that is blocked by G4 (the attestation message binds this record's
  `record_id`), NOT by G3 (the digest), and today additionally by G4 being
  fail-closed. `generation` is bound to `content_hash` like every other field, so
  tampering with declared provenance already breaks the P3 chain.
═══════════════════════════════════════════════════════════════════════════════
-/

namespace OmegaProvenance

/-! ## §1 The generation block and the (minimal) record -/

/-- Declared generation provenance. `promptHash` is optional; when present it is
    the 32-byte sha256 digest of the canonical prompt payload. `tool_versions`
    is not part of the checked property and is omitted from the model. -/
structure Generation where
  modelId      : String
  modelVersion : String
  promptHash   : Option (List UInt8)

/-- The record, reduced to the only slot this property reads. -/
structure ProvRecord where
  generation : Option Generation

/-! ## §2 The predicate -/

/-- Digest shape: a sha256 commitment is 32 bytes wide. -/
def hashWF (h : List UInt8) : Bool := decide (h.length = 32)

/-- prompt_hash is well-formed iff absent, or present with the bound shape. -/
def promptWF : Option (List UInt8) → Bool
  | none   => true
  | some h => hashWF h

/-- A generation block is well-formed iff both identifiers are non-empty and the
    optional prompt hash (if present) has the bound shape. -/
def genWF (g : Generation) : Bool :=
  (g.modelId != "") && (g.modelVersion != "") && promptWF g.promptHash

/-- P_VersionProvenance: presence + well-formedness. Pure and total — an external
    verifier re-runs it and gets the same Bool. -/
def hasProv (r : ProvRecord) : Bool :=
  match r.generation with
  | none   => false
  | some g => genWF g

/-! ## §3 Theorems (target: zero user axioms) -/

/-- The property is decidable: `hasProv` is a total Bool function. -/
theorem provenance_decidable (r : ProvRecord) :
    hasProv r = true ∨ hasProv r = false := by
  cases hasProv r <;> simp

/-- `hasProv` is a function, hence deterministic. -/
theorem provenance_deterministic (r : ProvRecord) (x y : Bool)
    (hx : x = hasProv r) (hy : y = hasProv r) : x = y := by
  rw [hx, hy]

/-- Absence lemma: a record with no generation block fails the property
    (it is not schema-forced — the property is evaluated). -/
theorem absence_fails (r : ProvRecord) (h : r.generation = none) :
    hasProv r = false := by
  simp only [hasProv, h]

/-- Well-formed prompt binding: if the property holds and a prompt hash is
    present, that hash has the bound 32-byte digest shape. -/
theorem wellformed_prompt_binding (r : ProvRecord) (g : Generation) (h : List UInt8)
    (hg : r.generation = some g) (hph : g.promptHash = some h)
    (hp : hasProv r = true) : h.length = 32 := by
  simp only [hasProv, hg, genWF, promptWF, hashWF, hph,
    Bool.and_eq_true, decide_eq_true_eq] at hp
  exact hp.2

/-- A holding property implies both identifiers are non-empty. -/
theorem presence_implies_identifiers (r : ProvRecord) (g : Generation)
    (hg : r.generation = some g) (hp : hasProv r = true) :
    g.modelId ≠ "" ∧ g.modelVersion ≠ "" := by
  simp only [hasProv, hg, genWF, Bool.and_eq_true, bne_iff_ne] at hp
  exact ⟨hp.1.1, hp.1.2⟩

/-! ## §4 Non-vacuity — both branches are reachable -/

/-- A concrete 32-byte digest witness. -/
def digest32 : List UInt8 := List.replicate 32 (0 : UInt8)

def goodRecord : ProvRecord :=
  { generation := some { modelId := "claude", modelVersion := "opus-4-8",
                         promptHash := some digest32 } }

def bareRecord : ProvRecord := { generation := none }

/-- The property is satisfiable AND refutable: not vacuously true or false. -/
theorem non_vacuity : hasProv goodRecord = true ∧ hasProv bareRecord = false := by
  decide

end OmegaProvenance
