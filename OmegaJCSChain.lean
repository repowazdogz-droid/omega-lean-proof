import OmegaP3Semantic
import OmegaJCS.Types
import OmegaJCS.Encode
import OmegaJCS.Decode
import OmegaJCS.Roundtrip

/-!
# Chain ↔ JCS bridge

This module connects the concrete hash-chain model of `OmegaP3Semantic` to the
RFC 8785 (JCS) profile encoder formalised in `OmegaJCS`.

**What this closes.** A `Record.payload` is, in the proof model, an opaque
`ByteArray`. Production sets that payload to the *canonical JSON* of a profile
value (the RFC 8785 subset: integers, scalars-only strings, UTF-16 key order),
and hashes it with SHA-256. `jsonPayload` identifies the proof-model payload with
exactly that production encoding (`canonicalBytesJCS`). With this identification,
`json_tamper_implies_collision` shows: **altering the JSON content of a sealed
record — in any field, to any other well-formed value — while keeping the chain
verifiable forces a SHA-256 collision.** The argument is constructive (no
injectivity or collision-resistance axiom): the encoding's machine-checked
injectivity (`canonicalBytesJCS_injective`) turns a JSON-level change into a
genuine payload change, and `tamper_implies_collision` turns a payload change
that still verifies into an explicit `compute_hash` collision.

**Remaining boundary (stated honestly).** The bytes that production SHA-256s are
the *full JSON envelope* (`seq`/`prev` framing serialised as JSON per SPEC §7);
the bytes this proof reasons about are the Lean binary record layout
(`Record.canonicalBytes`) carrying a JSON *payload*. The payload-level connection
is closed here; unifying the OUTER envelope (Lean binary framing vs the full-JSON
envelope) is tracked as future work.
-/

namespace OmegaJCSChain

open OmegaP3Semantic OmegaJCS

/-- The payload a production record actually carries: the canonical (RFC 8785
    profile) JSON encoding of a profile value. -/
def jsonPayload (v : OmegaJson) : ByteArray := canonicalBytesJCS v

/-- A record whose payload is the JCS encoding of a profile value. -/
def Record.HasJsonPayload (r : Record) (v : OmegaJson) : Prop :=
  v.WF ∧ r.payload = jsonPayload v

/-- Distinct well-formed profile values never share a canonical JSON payload.
    Immediate from the machine-checked encoder injectivity. -/
theorem jsonPayload_injective (v w : OmegaJson)
    (hv : v.WF) (hw : w.WF) :
    jsonPayload v = jsonPayload w → v = w := by
  intro h
  exact canonicalBytesJCS_injective v w hv hw h

/-- JSON-level tamper: same chain shape, one record's JSON value replaced by a
    different well-formed value. -/
def JsonTamper (chain tampered : List Record)
    (v v' : OmegaJson) : Prop :=
  v.WF ∧ v'.WF ∧ v ≠ v' ∧
  ∃ (pre suffix : List Record) (original : Record),
    original.payload = jsonPayload v ∧
    chain = pre ++ original :: suffix ∧
    tampered = pre ++
      { original with payload := jsonPayload v' } :: suffix

/-- A JSON-level tamper is, in particular, a payload-level tamper: the payload
    inequality is exactly the contrapositive of `jsonPayload_injective`
    (`v ≠ v' → jsonPayload v ≠ jsonPayload v'`). -/
theorem jsonTamper_implies_payloadTamper
    (chain tampered : List Record) (v v' : OmegaJson) :
    JsonTamper chain tampered v v' →
    PayloadTamper chain tampered := by
  intro ht
  obtain ⟨hv, hv', hne, pre, suffix, original, horig, hchain, htampered⟩ := ht
  refine ⟨pre, suffix, original, jsonPayload v', hchain, htampered, ?_⟩
  rw [horig]
  intro heq
  exact hne (jsonPayload_injective v' v hv' hv heq).symm

/-- **Main bridge theorem.** If a chain is traceable, a JSON-level tamper that
    leaves the chain traceable forces a SHA-256 collision. No injectivity or
    collision-resistance axiom is used. -/
theorem json_tamper_implies_collision
    (chain tampered : List Record) (v v' : OmegaJson) :
    P3_Traceability chain →
    JsonTamper chain tampered v v' →
    P3_Traceability tampered →
    ∃ a b : ByteArray, a ≠ b ∧ compute_hash a = compute_hash b := by
  intro hp ht htamp
  exact tamper_implies_collision chain tampered hp
    (jsonTamper_implies_payloadTamper chain tampered v v' ht) htamp

end OmegaJCSChain
