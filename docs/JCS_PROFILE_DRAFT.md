# OMEGA JCS Profile (Draft) — proposed SPEC §7.1

**Status:** Draft for contracts 0.3.0 migration. **Not** a shipped Lean root.

## Scope

This profile defines the JSON value domain and canonical serialization used when
computing OMEGA record `content_hash` under RFC 8785 (JSON Canonicalization Scheme).

## MUST requirements

1. **Serialization:** Values MUST be serialized with RFC 8785 rules (no whitespace;
   object keys sorted by UTF-16 code-unit lexicographic order; string escaping
   exactly as RFC 8785 — `\"`, `\\`, `\b`, `\f`, `\n`, `\r`, `\t`, `\u00XX`
   lowercase hex for U+0000–U+001F; all other Unicode as literal UTF-8 in output).

2. **Numbers:** Values MUST be JSON integers only, with `|n| ≤ 2^53 − 1`
   (JavaScript `Number.MAX_SAFE_INTEGER`). Non-integer numbers (floats, NaN,
   Infinity) are **excluded** from this profile. Trust scores and similar
   fractional fields MUST migrate to integer milli-units (0–1000) under
   contracts 0.3.0.

3. **Strings:** String values MUST be valid Unicode scalar sequences. Lone
   UTF-16 surrogates MUST NOT appear. (Note: npm `canonicalize@3.0.0` passes
   lone surrogates through; this profile forbids them. Lean `String`/`Char`
   cannot represent lone surrogates — this is a deliberate tightening.)

4. **Keys:** Object keys MUST be unique. Strict UTF-16 sorted key order implies
   uniqueness for well-formed objects.

5. **Null / bool / array / object:** Standard JSON forms; `undefined` and
   `symbol` properties are omitted (not in interchange JSON).

## Canonical bytes

`canonicalBytesJCS(v) := UTF-8 bytes of the JCS serialization of `v`.

## Migration note (0.2.x → 0.3.0)

- Records sealed under contracts **0.2.x** pin their schema/contracts version
  via P14; replay against 0.2.x rules remains valid for those records.
- **0.3.0** introduces integer milli-units for former 0–1 trust scores and
  removes non-integer numbers from the hash domain.
- Float policy **(A)** was chosen: exclude non-integers from the profile; spec
  migration runs separately from this Lean module.

## Verification

- Lean module `OmegaJCS` (non-shipped Lake target) implements encoder/decoder.
- Scratch corpus `lean-proof/scratch/jcs-cases/` is byte-for-byte checked against
  npm `canonicalize@3.0.0` on integer-only inputs.
- Roundtrip theorems (`decode_encode`, injectivity) are in `OmegaJCS.Roundtrip`
  (proofs in progress; `#print axioms` gate applies).
