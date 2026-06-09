-- OMEGA Protocol - P3 semantic traceability
-- Goal contract reference: /Users/warre/Omega/unified-forge/goal-contract.md
-- Goal: concrete P3 hash-chain model with PROVEN encoding injectivity.
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
--
-- Soundness fix applied 2026-06-09. The former axiom
-- `canonicalBytes_injective` was FALSE in this model and made the theory
-- inconsistent. Two counterexamples (both machine-checked below as
-- `old_axiom_was_false` and `old_axiom_was_false_seqnum`):
--   (a) seq_num : Nat is unbounded but encodeSeqNum truncates to 64 bits,
--       so seq_num = 0 and seq_num = 2^64 encode identically;
--   (b) encodePrevHash (some bs) = 0x01 ++ bs carries no length delimiter
--       and payload follows, so (prev = [0xAA], payload = [0xBB]) and
--       (prev = [0xAA, 0xBB], payload = []) encode identically.
-- The axiom is replaced by the PROVEN theorem `canonicalBytes_injective_wf`,
-- which restricts to well-formed records (`Record.WF`: seq_num < 2^64 and
-- any present prev_hash is exactly 32 bytes). Under WF the encoding is
-- prefix-free and a decoder (`decodeCanonical`) recovers all three fields;
-- injectivity follows from the decode/encode roundtrip. WF is threaded
-- through `P3_Traceability` so every downstream theorem carries it.

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

/-- Well-formedness: the operating range within which the canonical
    encoding is uniquely decodable.
    (1) `seq_num < 2^64` — the 8-byte big-endian prefix is faithful.
    (2) any present `prev_hash` is exactly 32 bytes (a SHA-256 digest) —
        the payload boundary after the 0x01 tag is recoverable.
    Outside this range the encoding is ambiguous (see the two
    `old_axiom_was_false*` counterexample theorems below). -/
def Record.WF (r : Record) : Prop :=
  r.seq_num < 2 ^ 64 ∧ ∀ bs, r.prev_hash = some bs → bs.size = 32

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

/-! ## Decoder

Under `Record.WF` the layout is prefix-free: bytes 0–7 are the big-endian
seq_num, byte 8 is the prev_hash tag (0x00 = none / 0x01 = some), if the
tag is 0x01 the next 32 bytes are the prev_hash digest, and the remainder
is the payload. The byte-level work is done over `List UInt8` (richer
lemma library than `ByteArray`); `ByteArray` is rebuilt at the edges via
`List.toByteArray`. -/

/-- Big-endian reconstruction of the first 8 bytes; ignores any tail.
    Stated arithmetically (`* 2^k + …`) rather than with `<<<`/`|||` so
    the roundtrip proof lands in `omega`'s fragment. -/
def decodeSeqNum : List UInt8 → Nat
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: _ =>
      b0.toNat * 2 ^ 56 + b1.toNat * 2 ^ 48 + b2.toNat * 2 ^ 40 +
      b3.toNat * 2 ^ 32 + b4.toNat * 2 ^ 24 + b5.toNat * 2 ^ 16 +
      b6.toNat * 2 ^ 8 + b7.toNat
  | _ => 0

/-- Full decoder: recovers `(seq_num, prev_hash, payload)` from the
    canonical byte stream, or `none` if the stream is malformed (too
    short, unknown tag, or truncated 32-byte digest block). -/
def decodeCanonical (bytes : List UInt8) : Option (Nat × Option ByteArray × ByteArray) :=
  match bytes with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: tag :: rest =>
      let seq := decodeSeqNum [b0, b1, b2, b3, b4, b5, b6, b7]
      if tag = 0x00 then
        some (seq, none, rest.toByteArray)
      else if tag = 0x01 then
        if 32 ≤ rest.length then
          some (seq, some (rest.take 32).toByteArray, (rest.drop 32).toByteArray)
        else
          none
      else
        none
  | _ => none

/-- The 8 literal bytes of the seq_num block, as a list. -/
private theorem encodeSeqNum_toList (n : Nat) :
    (encodeSeqNum n).data.toList =
      [UInt8.ofNat ((n >>> 56) &&& 0xFF), UInt8.ofNat ((n >>> 48) &&& 0xFF),
       UInt8.ofNat ((n >>> 40) &&& 0xFF), UInt8.ofNat ((n >>> 32) &&& 0xFF),
       UInt8.ofNat ((n >>> 24) &&& 0xFF), UInt8.ofNat ((n >>> 16) &&& 0xFF),
       UInt8.ofNat ((n >>> 8) &&& 0xFF), UInt8.ofNat (n &&& 0xFF)] := rfl

private theorem prevHash_none_toList :
    (encodePrevHash none).data.toList = [0x00] := rfl

private theorem prevHash_some_toList (bs : ByteArray) :
    (encodePrevHash (some bs)).data.toList = 0x01 :: bs.data.toList := by
  rw [encodePrevHash, ByteArray.toList_data_append]
  rfl

/-- Rebuilding a ByteArray from its own byte list is the identity. -/
private theorem toByteArray_toList (b : ByteArray) :
    b.data.toList.toByteArray = b :=
  ByteArray.ext (by simp)

/-- Big-endian reconstruction over the literal byte expressions. The
    single genuinely arithmetic step of the development. After rewriting
    `>>> k` to `/ 2^k`, `&&& 0xFF` to `% 2^8`, and `UInt8.toNat ∘
    UInt8.ofNat` to `% 2^8`, the identity is assembled one byte at a
    time via the mod ladder `n % 2^(k+8) = n / 2^k % 2^8 * 2^k + n % 2^k`
    (a single `omega` on the full 8-byte goal exceeds the heartbeat
    budget; each one-byte rung is trivial for it). -/
private theorem decodeSeqNum_literal (n : Nat) (h : n < 2 ^ 64) :
    decodeSeqNum
      [UInt8.ofNat ((n >>> 56) &&& 0xFF), UInt8.ofNat ((n >>> 48) &&& 0xFF),
       UInt8.ofNat ((n >>> 40) &&& 0xFF), UInt8.ofNat ((n >>> 32) &&& 0xFF),
       UInt8.ofNat ((n >>> 24) &&& 0xFF), UInt8.ofNat ((n >>> 16) &&& 0xFF),
       UInt8.ofNat ((n >>> 8) &&& 0xFF), UInt8.ofNat (n &&& 0xFF)] = n := by
  have hmask : ∀ x : Nat, x &&& 0xFF = x % 2 ^ 8 :=
    fun x => Nat.and_two_pow_sub_one_eq_mod x 8
  have hmm : ∀ x : Nat, x % 2 ^ 8 % 2 ^ 8 = x % 2 ^ 8 := fun x => by omega
  simp only [decodeSeqNum, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  simp only [hmask, hmm]
  have h08 : n / 2 ^ 8 % 2 ^ 8 * 2 ^ 8 + n % 2 ^ 8 = n % 2 ^ 16 := by omega
  have h16 : n / 2 ^ 16 % 2 ^ 8 * 2 ^ 16 + n % 2 ^ 16 = n % 2 ^ 24 := by omega
  have h24 : n / 2 ^ 24 % 2 ^ 8 * 2 ^ 24 + n % 2 ^ 24 = n % 2 ^ 32 := by omega
  have h32 : n / 2 ^ 32 % 2 ^ 8 * 2 ^ 32 + n % 2 ^ 32 = n % 2 ^ 40 := by omega
  have h40 : n / 2 ^ 40 % 2 ^ 8 * 2 ^ 40 + n % 2 ^ 40 = n % 2 ^ 48 := by omega
  have h48 : n / 2 ^ 48 % 2 ^ 8 * 2 ^ 48 + n % 2 ^ 48 = n % 2 ^ 56 := by omega
  have h56 : n / 2 ^ 56 % 2 ^ 8 * 2 ^ 56 + n % 2 ^ 56 = n % 2 ^ 64 := by omega
  simp only [Nat.add_assoc]
  rw [h08, h16, h24, h32, h40, h48, h56, Nat.mod_eq_of_lt h]

/-- Roundtrip for the 8-byte big-endian seq_num block. -/
theorem decodeSeqNum_encode (n : Nat) (h : n < 2 ^ 64) :
    decodeSeqNum (encodeSeqNum n).data.toList = n := by
  rw [encodeSeqNum_toList]
  exact decodeSeqNum_literal n h

/-- The canonical bytes of a record, as a list, split into the three
    layout blocks. -/
private theorem canonicalBytes_toList (r : Record) :
    r.canonicalBytes.data.toList =
      (encodeSeqNum r.seq_num).data.toList ++
      (encodePrevHash r.prev_hash).data.toList ++
      r.payload.data.toList := by
  simp [Record.canonicalBytes]

/-- Decode/encode roundtrip on well-formed records: the decoder recovers
    exactly the three hash-bound fields. -/
theorem decode_encode (r : Record) (h : r.WF) :
    decodeCanonical r.canonicalBytes.data.toList =
      some (r.seq_num, r.prev_hash, r.payload) := by
  obtain ⟨hseq, hprev⟩ := h
  rw [canonicalBytes_toList, encodeSeqNum_toList]
  cases hp : r.prev_hash with
  | none =>
      -- Layout: seq(8) ++ [0x00] ++ payload
      rw [prevHash_none_toList]
      simp only [List.cons_append, List.nil_append]
      simp only [decodeCanonical]
      rw [decodeSeqNum_literal r.seq_num hseq]
      simp only [toByteArray_toList]
      simp
  | some bs =>
      -- Layout: seq(8) ++ [0x01] ++ bs(32) ++ payload
      have hbs : bs.size = 32 := hprev bs hp
      have hlen : bs.data.toList.length = 32 := by
        simpa using hbs
      rw [prevHash_some_toList]
      simp only [List.cons_append, List.nil_append]
      simp only [decodeCanonical]
      rw [decodeSeqNum_literal r.seq_num hseq,
        List.take_left' hlen, List.drop_left' hlen]
      simp only [toByteArray_toList]
      have hge : 32 ≤ bs.size + r.payload.size := by omega
      simp [hge]

/-- PROVEN replacement for the deleted `canonicalBytes_injective` axiom:
    on well-formed records the canonical encoding is injective in the
    three hash-bound fields. Proof: rewrite both sides through
    `decode_encode` and use injectivity of `Option.some` / `Prod.mk`.
    Depends on no user axioms. -/
theorem canonicalBytes_injective_wf :
    ∀ r1 r2 : Record, r1.WF → r2.WF →
    r1.canonicalBytes = r2.canonicalBytes →
    r1.seq_num = r2.seq_num ∧ r1.prev_hash = r2.prev_hash ∧
    r1.payload = r2.payload := by
  intro r1 r2 h1 h2 heq
  have hd1 := decode_encode r1 h1
  have hd2 := decode_encode r2 h2
  rw [← heq] at hd2
  have htup : (r1.seq_num, r1.prev_hash, r1.payload)
      = (r2.seq_num, r2.prev_hash, r2.payload) :=
    Option.some.inj (hd1.symm.trans hd2)
  exact ⟨congrArg Prod.fst htup,
    congrArg (fun p => p.snd.fst) htup,
    congrArg (fun p => p.snd.snd) htup⟩

/-! ## Negative regression: the old axiom was refutable

The two theorems below permanently document the soundness bug. Each
constructs concrete records that encode identically while disagreeing on
a hash-bound field — directly contradicting the former unconditional
`canonicalBytes_injective` axiom. Both records in each pair violate
`Record.WF`, which is exactly why the proven replacement theorem
restricts to WF records. -/

/-- Counterexample (b) — framing ambiguity: with no length delimiter on
    the prev_hash block, bytes can migrate between prev_hash and payload.
    (prev = [0xAA], payload = [0xBB]) and (prev = [0xAA, 0xBB],
    payload = []) produce the same canonical bytes.
    Witness records are NOT WF: r1.prev_hash = some #[0xAA] has size 1 ≠ 32. -/
theorem old_axiom_was_false :
    ∃ r1 r2 : Record, r1.canonicalBytes = r2.canonicalBytes ∧
      r1.payload ≠ r2.payload := by
  refine ⟨
    { content_hash := ByteArray.empty
      prev_hash := some (ByteArray.mk #[0xAA])
      payload := ByteArray.mk #[0xBB]
      seq_num := 0
      goal_contract_ref := ""
      author_agent := ""
      review_status := "" },
    { content_hash := ByteArray.empty
      prev_hash := some (ByteArray.mk #[0xAA, 0xBB])
      payload := ByteArray.empty
      seq_num := 0
      goal_contract_ref := ""
      author_agent := ""
      review_status := "" }, ?_, ?_⟩
  · exact ByteArray.ext (by decide)
  · exact fun h => absurd (congrArg ByteArray.size h) (by decide)

/-- Counterexample (a) — 64-bit truncation: seq_num : Nat is unbounded
    but encodeSeqNum keeps only the low 64 bits, so seq_num = 0 and
    seq_num = 2^64 encode identically.
    Witness records are NOT WF: r2.seq_num = 2^64 violates seq_num < 2^64. -/
theorem old_axiom_was_false_seqnum :
    ∃ r1 r2 : Record, r1.canonicalBytes = r2.canonicalBytes ∧
      r1.seq_num ≠ r2.seq_num := by
  refine ⟨
    { content_hash := ByteArray.empty
      prev_hash := none
      payload := ByteArray.empty
      seq_num := 0
      goal_contract_ref := ""
      author_agent := ""
      review_status := "" },
    { content_hash := ByteArray.empty
      prev_hash := none
      payload := ByteArray.empty
      seq_num := 2 ^ 64
      goal_contract_ref := ""
      author_agent := ""
      review_status := "" }, ?_, ?_⟩
  · exact ByteArray.ext (by decide)
  · decide

-- Hash primitive intended to be SHA-256. Declared `opaque` so the kernel
-- treats it as a function whose implementation exists but is not unfolded
-- during proof checking. This is a stronger claim than `axiom` (which only
-- asserts existence) — it commits to "there is a real function here that
-- will be supplied at runtime" without forcing the supply now. The
-- intended runtime backing is libsodium's `crypto_hash_sha256` via FFI,
-- to be wired up in a separate step that needs the libsodium toolchain.
--
-- TODO(VCVio): replace with `VCVio.CryptoFoundations.HardnessAssumptions.CollisionResistance`
-- oracle-model proof once `LibSodium/SHA2.lean` is populated (empty at v4.27.0).
-- Probe import: `lean-proof/probes/VCVioProbe.lean`. See `docs/lean-axioms.md` and
-- `lean-proof/VCVIO_MIGRATION.md`.
opaque compute_hash : ByteArray → ByteArray

-- Collision resistance: SHA-256 is not truly injective but is computationally
-- collision-resistant, meaning no efficient algorithm can find a b ≠ a with the
-- same hash. This is the standard cryptographic assumption, not provable in
-- pure Lean. Without this, tamper_detection cannot be proved — a malicious
-- payload would only have to produce a hash collision rather than the same
-- payload bytes.
--
-- MODELING NOTE — trust boundary (NOT changed in the 2026-06-09 soundness
-- pass; this is the package's sole remaining user axiom):
-- The axiom below asserts true INJECTIVITY of compute_hash
-- (compute_hash a = compute_hash b → a = b), which is *strictly stronger*
-- than SHA-256's actual property of collision resistance. SHA-256 cannot be
-- injective: it maps arbitrary-length inputs to a fixed 256-bit output, so
-- collisions must exist by pigeonhole. Unlike the deleted
-- canonicalBytes_injective axiom this one is SATISFIABLE in the model —
-- compute_hash is opaque with no defining equations, so an injective
-- interpretation (e.g. the identity function) exists and the axiom cannot
-- introduce an inconsistency. It is a deliberate idealisation: any
-- soundness claim flowing through `tamper_detection` depends on the
-- absence of an exhibited SHA-256 collision in the runtime artifacts being
-- checked, and is *not* a claim about SHA-256's mathematical structure.
-- PLANNED REPLACEMENT: a VCVio game-based reduction (negligible collision
-- advantage over a security parameter) once the toolchain supports it —
-- see VCVIO_MIGRATION.md.
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
-- (1) every record is well-formed (seq_num < 2^64, 32-byte prev_hash) —
--     added in the 2026-06-09 soundness pass so encoding injectivity is
--     available without an axiom,
-- (2) each record's content_hash matches its canonical bytes,
-- (3) prev_hash linkage from genesis to tip,
-- (4) seq_num contiguity (no gaps).
def P3_Traceability (chain : List Record) : Prop :=
  (∀ r ∈ chain, r.WF) ∧
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
-- The former residual assumptions (seq_num < 2^64, 32-byte prev_hash) are
-- no longer silent: they are the explicit `r.WF` hypothesis below and the
-- WF conjunct of P3_Traceability.
-- AXIOM DEPENDENCIES: none beyond Lean built-ins (propext).
theorem chain_integrity_extends (chain : List Record) (r : Record) :
    P3_Traceability chain →
    r.WF →
    r.content_hash = compute_hash r.canonicalBytes →
    r.prev_hash = next_prev_hash chain →
    r.seq_num = chain.length →
    P3_Traceability (chain ++ [r]) := by
  intro hp hwf hhash hprev hseq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    simp at hx
    rcases hx with hx | hx
    · exact hp.1 x hx
    · cases hx
      exact hwf
  · intro x hx
    simp at hx
    rcases hx with hx | hx
    · exact hp.2.1 x hx
    · cases hx
      exact hhash
  · exact linked_from_append_single none chain r hp.2.2.1 hprev
  · intro i hi
    by_cases hleft : i < chain.length
    · rw [List.getElem_append_left hleft]
      exact hp.2.2.2 i hleft
    · have hi' : i < chain.length + 1 := by
        simpa [List.length_append] using hi
      have hieq : i = chain.length :=
        Nat.eq_of_lt_succ_of_not_lt hi' hleft
      subst i
      have hle : chain.length ≤ chain.length := Nat.le_refl chain.length
      rw [List.getElem_append_right hle]
      simp [hseq]

-- AXIOM DEPENDENCIES: none beyond Lean built-ins.
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

-- Proof using compute_hash_collision_resistant + canonicalBytes_injective_wf.
-- Sketch: in the tampered chain the tampered record's content_hash is
-- unchanged from the original (structure update only changes payload). If
-- P3_Traceability holds on the tampered chain, both records' content_hash
-- equal compute_hash of their respective canonicalBytes. Collision
-- resistance lifts that to canonicalBytes equality; the proven injectivity
-- theorem (both records are WF — tampering the payload does not affect WF,
-- and the original is WF from the original chain's P3) then forces payload
-- equality, contradicting the tamper hypothesis.
--
-- DEPENDENCY MINIMISATION NOTE: both steps are genuinely needed. Collision
-- resistance only equates the *byte streams* (canonicalBytes); without
-- encoding injectivity, equal byte streams would not force equal payloads
-- (the two counterexample theorems above show exactly how equal bytes can
-- hide different field values outside WF). With WF available from
-- P3_Traceability, injectivity is now a theorem, so the only user axiom
-- in this proof is compute_hash_collision_resistant.
-- AXIOM DEPENDENCIES: [propext, compute_hash_collision_resistant].
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
    exact List.mem_append_right pre (List.Mem.head suffix)
  -- Membership of original in the chain.
  have h_in_orig : original ∈ chain := by
    rw [hchain]
    exact List.mem_append_right pre (List.Mem.head suffix)
  -- Well-formedness of the original record, from the original chain.
  have h_orig_wf : original.WF := hp.1 original h_in_orig
  -- Well-formedness of the tampered record: a payload change touches
  -- neither seq_num nor prev_hash, so WF transfers from the original.
  have h_tamp_wf : tamperedRec.WF := ⟨h_orig_wf.1, h_orig_wf.2⟩
  -- Hash claim from P3_Traceability on the tampered chain.
  have h_tamp_hash :
      tamperedRec.content_hash = compute_hash tamperedRec.canonicalBytes :=
    htamp.2.1 tamperedRec h_in_tamp
  -- Hash claim from P3_Traceability on the original chain.
  have h_orig_hash :
      original.content_hash = compute_hash original.canonicalBytes :=
    hp.2.1 original h_in_orig
  -- Chain the equalities at the canonicalBytes level.
  have h_hash_eq :
      compute_hash tamperedRec.canonicalBytes = compute_hash original.canonicalBytes := by
    rw [← h_tamp_hash, h_ch_eq, h_orig_hash]
  -- Collision resistance yields canonicalBytes equality.
  have h_cb_eq : tamperedRec.canonicalBytes = original.canonicalBytes :=
    compute_hash_collision_resistant _ _ h_hash_eq
  -- Proven injectivity on WF records (formerly an unsound axiom).
  have h_payload_eq : tamperedRec.payload = original.payload :=
    (canonicalBytes_injective_wf tamperedRec original h_tamp_wf h_orig_wf h_cb_eq).2.2
  -- tamperedRec.payload reduces to changedPayload via the structure update,
  -- so this contradicts the PayloadTamper hypothesis.
  exact hpayload h_payload_eq

-- Without seq_num contiguity, the chain [r0(seq=0), r1(seq=1), r3(seq=3)]
-- could satisfy the prev_hash linkage while skipping seq 2. This theorem
-- extracts the contiguity guarantee directly from P3_Traceability.
-- AXIOM DEPENDENCIES: none.
theorem chain_no_gaps (chain : List Record) :
    P3_Traceability chain →
    ∀ (i : Nat) (h : i < chain.length), chain[i].seq_num = i := by
  intro hp i h
  exact hp.2.2.2 i h

-- Every record in a traceable chain is well-formed. Direct projection of
-- the WF conjunct added in the 2026-06-09 soundness pass.
-- AXIOM DEPENDENCIES: none.
theorem chain_all_wf (chain : List Record) :
    P3_Traceability chain →
    ∀ r ∈ chain, r.WF := by
  intro hp
  exact hp.1

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
