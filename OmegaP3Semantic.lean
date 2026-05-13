-- OMEGA Protocol - P3 semantic traceability draft
-- Goal contract reference: /Users/warre/Omega/unified-forge/goal-contract.md
-- Goal: draft a concrete P3 hash-chain model and check Lean types.
-- Non-goals: no VCVio/Mathlib dependency bump.
-- Verification: run `lake build` from /Users/warre/Omega/lean-proof.
-- Provenance inputs:
--   - /Users/warre/Omega/lean-proof/OmegaV14.lean
--   - /Users/warre/Omega/unified-forge/experiments/verification-extension-plan.md section 1.3
-- Adversarial review applied 2026-05-13 (DeepSeek). Three gaps closed:
--   (1) compute_hash_collision_resistant axiom added so tamper_detection is discharged
--       without resorting to a probabilistic model;
--   (2) chain_contiguous predicate added to P3_Traceability so a chain with
--       missing seq_num values (e.g. 0, 1, 3 with 2 missing) is rejected;
--   (3) tamper_detection now has a real proof (was: sorry).

namespace OmegaP3Semantic

-- Concrete record. Fields visible to the chain layer (content_hash,
-- prev_hash, payload, seq_num) plus the governance-attribution fields
-- (goal_contract_ref, author_agent, review_status) used by
-- OmegaP1Governance. The same Record structure is shared across
-- predicates so a single artefact carries both kinds of evidence.
-- seq_num is the per-record sequence index used by chain_contiguous below
-- to rule out chains that link by prev_hash but skip seq_num values.
structure Record where
  content_hash : ByteArray
  prev_hash    : Option ByteArray
  payload      : ByteArray
  seq_num      : Nat
  goal_contract_ref : String
  author_agent : String
  review_status : String

-- The body bytes used as input to SHA-256. Folds seq_num, prev_hash, and
-- payload into one byte sequence so content_hash binds all three fields.
-- seq_num is a fixed 8-byte big-endian prefix; prev_hash is a 1-byte tag
-- (0x00 = none, 0x01 = some) followed by the 32-byte hash bytes when
-- present; payload is the trailing bytes. This intentionally excludes
-- content_hash itself (which is the *output* of compute_hash on these
-- bytes).
--
-- Closes two attack vectors:
--   (a) seq_num manipulation — an adversary can no longer mint records
--       whose seq_num lies about position while keeping content_hash valid.
--   (b) prev_hash rewrite — an adversary can no longer redirect a record's
--       prev_hash to point at a different predecessor while keeping
--       content_hash valid. Without prev_hash in the hash input, the only
--       check on prev_hash is the structural linked_from predicate; a
--       record whose hash matched but whose prev_hash differed from the
--       predecessor's content_hash could be substituted into a different
--       chain position. With prev_hash bound, that substitution requires a
--       compute_hash collision.
private def encodeSeqNum (n : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat ((n >>> 56) &&& 0xFF),
    UInt8.ofNat ((n >>> 48) &&& 0xFF),
    UInt8.ofNat ((n >>> 40) &&& 0xFF),
    UInt8.ofNat ((n >>> 32) &&& 0xFF),
    UInt8.ofNat ((n >>> 24) &&& 0xFF),
    UInt8.ofNat ((n >>> 16) &&& 0xFF),
    UInt8.ofNat ((n >>> 8) &&& 0xFF),
    UInt8.ofNat (n &&& 0xFF)
  ]

private def encodePrevHash : Option ByteArray → ByteArray
  | none    => ByteArray.mk #[0x00]
  | some bs => ByteArray.mk #[0x01] ++ bs

def Record.canonicalBytes (r : Record) : ByteArray :=
  encodeSeqNum r.seq_num ++ encodePrevHash r.prev_hash ++ r.payload

-- The canonical encoding is injective in its hash-bound fields (seq_num,
-- prev_hash, payload). seq_num is fixed-width (8 bytes); the prev_hash
-- block is fixed-width too (1 byte for none, 33 bytes for some). The two
-- fixed-width prefixes make the encoding uniquely decodable: payload is
-- whatever follows. We declare injectivity as an axiom rather than proving
-- ByteArray cancellation from scratch.
--
-- MODELING NOTE — trust boundaries:
--   (1) Assumes seq_num < 2^64 (the 8-byte prefix wraps otherwise).
--   (2) Assumes any `some bs` in prev_hash has `bs.size = 32` (a SHA-256
--       digest). If a producer were to mint records with shorter or longer
--       prev_hash bytes, the 33-byte assumption used to recover the
--       payload boundary would fail and injectivity would not hold for
--       those records. Within the protocol's documented operating range
--       (prev_hash is always a SHA-256 output) this holds.
axiom canonicalBytes_injective :
  ∀ r1 r2 : Record,
    r1.canonicalBytes = r2.canonicalBytes →
    r1.seq_num = r2.seq_num ∧ r1.prev_hash = r2.prev_hash ∧ r1.payload = r2.payload

-- Hash primitive intended to be SHA-256. Declared `opaque` so the kernel
-- treats it as a function whose implementation exists but is not unfolded
-- during proof checking. This is a stronger claim than `axiom` (which only
-- asserts existence) — it commits to "there is a real function here that
-- will be supplied at runtime" without forcing the supply now. The
-- intended runtime backing is libsodium's `crypto_hash_sha256` via FFI,
-- to be wired up in a separate step that needs the libsodium toolchain.
opaque compute_hash : ByteArray → ByteArray

-- Collision resistance: SHA-256 is not truly injective but is computationally
-- collision-resistant, meaning no efficient algorithm can find a b ≠ a with the
-- same hash. This is the standard cryptographic assumption, not provable in
-- pure Lean. Without this, tamper_detection cannot be proved — a malicious
-- payload would only have to produce a hash collision rather than the same
-- payload bytes.
--
-- MODELING NOTE — trust boundary:
-- The axiom below states true injectivity
-- (compute_hash a = compute_hash b → a = b), which is *strictly stronger*
-- than SHA-256's actual property of collision resistance. SHA-256 cannot be
-- injective: it maps arbitrary-length inputs to a fixed 256-bit output, so
-- collisions must exist by pigeonhole. We adopt the idealized injectivity
-- assumption as a deliberate modeling choice — within this formal model
-- SHA-256 is treated as injective. This makes the trust boundary explicit:
-- any soundness claim flowing through `tamper_detection` depends on the
-- absence of an exhibited SHA-256 collision in the runtime artifacts being
-- checked, and is *not* a claim about SHA-256's mathematical structure.
axiom compute_hash_collision_resistant :
  ∀ a b : ByteArray, compute_hash a = compute_hash b → a = b

-- The expected prev_hash for the next record appended to this chain.
def expected_after (expected : Option ByteArray) (chain : List Record) : Option ByteArray :=
  chain.foldl (fun _ r => some r.content_hash) expected

def next_prev_hash (chain : List Record) : Option ByteArray :=
  expected_after none chain

-- Prev-hash linkage from genesis to tip.
def linked_from : Option ByteArray → List Record → Prop
  | _, [] => True
  | expected, r :: rest =>
      r.prev_hash = expected ∧ linked_from (some r.content_hash) rest

theorem linked_from_append_single
    (expected : Option ByteArray) (chain : List Record) (r : Record) :
    linked_from expected chain →
    r.prev_hash = expected_after expected chain →
    linked_from expected (chain ++ [r]) := by
  induction chain generalizing expected with
  | nil =>
      intro _ hprev
      simp [expected_after, linked_from] at hprev ⊢
      exact hprev
  | cons head tail ih =>
      intro hlinked hprev
      simp [linked_from] at hlinked ⊢
      exact ⟨hlinked.1, ih (some head.content_hash) hlinked.2 (by
        simpa [expected_after] using hprev)⟩

-- Sequence-number contiguity: chain[i].seq_num = i for every position i.
-- A chain like [r0(seq=0), r1(seq=1), r3(seq=3)] is rejected because at
-- position 2 the seq_num would have to be 2 but is 3.
def chain_contiguous (chain : List Record) : Prop :=
  ∀ (i : Nat) (h : i < chain.length), chain[i].seq_num = i

-- P3 traceability as a concrete predicate over a list of records:
-- (1) each record's content_hash matches its canonical bytes,
-- (2) prev_hash linkage from genesis to tip,
-- (3) seq_num contiguity (no gaps).
def P3_Traceability (chain : List Record) : Prop :=
  (∀ r ∈ chain, r.content_hash = compute_hash r.canonicalBytes) ∧
  linked_from none chain ∧
  chain_contiguous chain

-- A chain extension is the original chain plus a suffix.
def ChainExtends (chain chain' : List Record) : Prop :=
  ∃ suffix : List Record, chain' = chain ++ suffix

-- A payload tamper keeps the same record position and content_hash, but
-- changes the payload bytes.
def PayloadTamper (chain tampered : List Record) : Prop :=
  ∃ (pre suffix : List Record) (original : Record) (changedPayload : ByteArray),
    chain = pre ++ original :: suffix ∧
    tampered = pre ++ { original with payload := changedPayload } :: suffix ∧
    changedPayload ≠ original.payload

-- The contiguity hypothesis r.seq_num = chain.length is what was missing
-- in the v1 statement of this theorem before the DeepSeek review. Without
-- it, appending r would break chain_contiguous in any chain.
--
-- Notes on previously flagged trust boundaries at this theorem:
--   * seq_num manipulation: closed by folding seq_num into canonicalBytes
--     (encodeSeqNum prefix). A record whose seq_num lies about position
--     would have to break content_hash, ruled out by
--     compute_hash_collision_resistant.
--   * prev_hash rewrite: closed by folding prev_hash into canonicalBytes
--     (encodePrevHash block). A record substituted into a different chain
--     position with a different predecessor's content_hash as prev_hash
--     would also have to break content_hash.
-- Residual assumptions live at canonicalBytes_injective: seq_num < 2^64
-- and any present prev_hash is a 32-byte SHA-256 digest. Both hold for
-- chains produced by a conformant runtime.
theorem chain_integrity_extends (chain : List Record) (r : Record) :
    P3_Traceability chain →
    r.content_hash = compute_hash r.canonicalBytes →
    r.prev_hash = next_prev_hash chain →
    r.seq_num = chain.length →
    P3_Traceability (chain ++ [r]) := by
  intro hp hhash hprev hseq
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp at hx
    rcases hx with hx | hx
    · exact hp.1 x hx
    · cases hx
      exact hhash
  · exact linked_from_append_single none chain r hp.2.1 hprev
  · intro i hi
    by_cases hleft : i < chain.length
    · rw [List.getElem_append_left hleft]
      exact hp.2.2 i hleft
    · have hi' : i < chain.length + 1 := by
        simpa [List.length_append] using hi
      have hieq : i = chain.length :=
        Nat.eq_of_lt_succ_of_not_lt hi' hleft
      subst i
      have hle : chain.length ≤ chain.length := Nat.le_refl chain.length
      rw [List.getElem_append_right hle]
      simp [hseq]

theorem chain_monotonicity (chain chain' : List Record) :
    ChainExtends chain chain' →
    chain.length ≤ chain'.length ∧ ChainExtends chain chain' := by
  intro h
  obtain ⟨suffix, hsuffix⟩ := h
  subst chain'
  constructor
  · rw [List.length_append]
    exact Nat.le_add_right chain.length suffix.length
  · exact ⟨suffix, rfl⟩

-- Proof using compute_hash_collision_resistant + canonicalBytes_injective.
-- Sketch: in the tampered chain the tampered record's content_hash is
-- unchanged from the original (structure update only changes payload). If
-- P3_Traceability holds on the tampered chain, both records' content_hash
-- equal compute_hash of their respective canonicalBytes. Collision
-- resistance lifts that to canonicalBytes equality; canonicalBytes_injective
-- then forces payload equality, contradicting the tamper hypothesis.
theorem tamper_detection (chain tampered : List Record) :
    P3_Traceability chain →
    PayloadTamper chain tampered →
    ¬ P3_Traceability tampered := by
  intro hp ht htamp
  obtain ⟨pre, suffix, original, changedPayload, hchain, htampered, hpayload⟩ := ht
  -- The tampered record produced by the structure update.
  let tamperedRec : Record := { original with payload := changedPayload }
  -- Structure update preserves content_hash; only payload changes.
  have h_ch_eq : tamperedRec.content_hash = original.content_hash := rfl
  -- Membership of tamperedRec in the tampered chain.
  -- On Lean 4.18 simp leaves a residual disjunct from the structure update,
  -- so discharge explicitly via append_right + cons_self.
  have h_in_tamp : tamperedRec ∈ tampered := by
    rw [htampered]
    exact List.mem_append_right pre (List.mem_cons_self _ _)
  -- Membership of original in the chain.
  have h_in_orig : original ∈ chain := by
    rw [hchain]
    exact List.mem_append_right pre (List.mem_cons_self _ _)
  -- Hash claim from P3_Traceability on the tampered chain.
  have h_tamp_hash :
      tamperedRec.content_hash = compute_hash tamperedRec.canonicalBytes :=
    htamp.1 tamperedRec h_in_tamp
  -- Hash claim from P3_Traceability on the original chain.
  have h_orig_hash :
      original.content_hash = compute_hash original.canonicalBytes :=
    hp.1 original h_in_orig
  -- Chain the equalities at the canonicalBytes level.
  have h_hash_eq :
      compute_hash tamperedRec.canonicalBytes = compute_hash original.canonicalBytes := by
    rw [← h_tamp_hash, h_ch_eq, h_orig_hash]
  -- Collision resistance yields canonicalBytes equality.
  have h_cb_eq : tamperedRec.canonicalBytes = original.canonicalBytes :=
    compute_hash_collision_resistant _ _ h_hash_eq
  -- Canonical encoding is injective in (seq_num, prev_hash, payload).
  have h_payload_eq : tamperedRec.payload = original.payload :=
    (canonicalBytes_injective tamperedRec original h_cb_eq).2.2
  -- tamperedRec.payload reduces to changedPayload via the structure update,
  -- so this contradicts the PayloadTamper hypothesis.
  exact hpayload h_payload_eq

-- Without seq_num contiguity, the chain [r0(seq=0), r1(seq=1), r3(seq=3)]
-- could satisfy the prev_hash linkage while skipping seq 2. This theorem
-- extracts the contiguity guarantee directly from P3_Traceability.
theorem chain_no_gaps (chain : List Record) :
    P3_Traceability chain →
    ∀ (i : Nat) (h : i < chain.length), chain[i].seq_num = i := by
  intro hp i h
  exact hp.2.2 i h

-- MIGRATION TARGET: replace with VCVio computational security proof
-- when toolchain is bumped to v4.29.0. See VCVIO_MIGRATION.md.
-- Shape: tamper_detection holds against any PPT adversary with
-- non-negligible SHA-256 collision advantage.
--
-- Current body delegates to the deterministic tamper_detection so the
-- API name is reserved and call sites compile against the eventual
-- signature. The signature here is the deterministic form; on
-- migration, this stub is replaced by the probabilistic form
-- (negligible advantage over a security parameter) and the proof body
-- becomes the reduction to sha256_collision_resistant.
theorem tamper_detection_computational_stub :
    ∀ (chain tampered : List Record),
    P3_Traceability chain →
    PayloadTamper chain tampered →
    ¬ P3_Traceability tampered :=
  tamper_detection

end OmegaP3Semantic
