# Assurance boundary — omega-lean-proof (Doctrine)

Lean artifacts are meaningful only **inside an explicit boundary**. `omega-lean-proof` formalises named predicates and lemmas over those definitions. It does not attest that production systems, records, or runtime gates satisfy those predicates.

---

## omega-lean-proof provides

| Capability | Mechanism |
| --- | --- |
| **Named doctrine predicates** | `Governed`, P-family atoms, hash-chain lemmas in shipped Lean roots |
| **Lean conjunction structure** | `Governed → P_i` projections, `¬P_i → ¬Governed` absence lemmas, packaging theorems |
| **SymPy failure-mode necessity (9/15)** | [`documents/necessity_all15.py`](../documents/necessity_all15.py) SHA `0ab3a965…`: domain-grounded \(F_i\), `g2` name guard, hard shared-flipped-literal guard |
| **Reproducible build receipts** | `lake build` @ Lean v4.27.0, `#print axioms`, SafeVerify replay (2026-05-19 pass) |
| **Explicit axiom posture** | Exactly ONE named user axiom: `compute_hash_collision_resistant` in `OmegaP3Semantic` (plus the `opaque compute_hash` declaration it constrains). The former second axiom `canonicalBytes_injective` was removed 2026-06-09 — see changelog below. |

---

## omega-lean-proof does NOT provide

| Non-guarantee | Implication |
| --- | --- |
| **Deployment attestation** | A clean Lean build does not prove a live system is governed |
| **Failure-mode necessity for all 15 primitives** | Only nine pass CLEAN in SymPy; six are design rationale (five proxy, PCF resistant) |
| **Sufficiency / independence / irreducibility theorems** | No committed runnable check establishes these for the full primitive set |
| **Runtime enforcement** | No gate evaluator, blocker, or router is shipped from this repo |
| **Record population** | Lean exports are **not embedded** in `@omega-protocol/contracts` records today |
| **Compliance certification** | Formal predicates are not regulatory guarantees |

Lean proves properties of **definitions**. SymPy proves failure-mode reachability only for the nine CLEAN primitives under stated domain encodings. Integrators must not treat theorem names as evidence that a deployment satisfies them.

---

## SymPy vs Lean (do not conflate)

| Claim | Established by |
| --- | --- |
| `Governed` is a conjunction; each conjunct is necessary for `Governed` in the Lean sense | `OmegaProof.lean`, `OmegaV14.lean` (projection / absence lemmas) |
| Removing P1 allows ungoverned-action worlds in a domain encoding | `documents/necessity_all15.py` (nine primitives only) |
| P2, P4M, P4T, P6A, P6L, PCF block named failures in all deployments | **Not established** — adversarial registry + design rationale |

---

## Trusted computing base (TCB)

| Component | Assumed correct |
| --- | --- |
| **Lean 4 kernel + toolchain pin** | `leanprover/lean4:v4.27.0` in [`lean-toolchain`](../lean-toolchain) |
| **Shipped Lean roots** | Seven Lake targets, zero `sorry` in shipped modules |
| **SafeVerify replay** | SafeVerify `main` @ Lean v4.27.0 (2026-05-19 pass on `OmegaProof.olean`, `OmegaV14.olean`) |
| **SymPy harness** | `documents/necessity_all15.py` encodings and satisfiability checks |
| **Reader interpretation** | Distinction between scaffolding, SymPy slice, and deployment claims |

**Outside the TCB:** sibling protocol libraries, runtime gates, production attestation.

---

## Contracts integration

See [omega-contracts PRIMITIVE_MAP](https://github.com/repowazdogz-droid/omega-contracts/blob/main/docs/PRIMITIVE_MAP.md): Lean is **doctrine / conceptual** relative to record slots. See also [TRUST_STACK](https://github.com/repowazdogz-droid/omega-contracts/blob/main/docs/TRUST_STACK.md).

Public doctrine page (aligned with this file): [omegaprotocol.org/omega/formal-proof/](https://omegaprotocol.org/omega/formal-proof/)

---

## Changelog

### 2026-06-09 — `canonicalBytes_injective` axiom removed (was false)

The axiom `canonicalBytes_injective` — unconditional injectivity of the
canonical record encoding in `(seq_num, prev_hash, payload)` — was found to
be **false in the model**, making the theory inconsistent. Two
counterexamples:

1. **64-bit truncation:** `seq_num : Nat` is unbounded but `encodeSeqNum`
   keeps only the low 64 bits, so `seq_num = 0` and `seq_num = 2^64` encode
   identically.
2. **Framing ambiguity:** `encodePrevHash (some bs) = 0x01 ++ bs` carries no
   length delimiter and the payload follows immediately, so
   `(prev = [0xAA], payload = [0xBB])` and
   `(prev = [0xAA, 0xBB], payload = [])` encode identically.

The axiom was **removed** and replaced by the **proven theorem**
`canonicalBytes_injective_wf`, which restricts injectivity to well-formed
records (`Record.WF`: `seq_num < 2^64` and any present `prev_hash` is
exactly 32 bytes). The proof goes through an explicit decoder
(`decodeCanonical`) and its roundtrip theorem (`decode_encode`); both
depend on no user axioms. `Record.WF` is threaded through
`P3_Traceability` as a new conjunct so every chain-level theorem
(`chain_integrity_extends`, `tamper_detection`, `valid_chain_extend`)
carries well-formedness explicitly rather than assuming it silently.

Both counterexamples are **machine-checked and kept in the codebase** as
negative regression theorems (`old_axiom_was_false`,
`old_axiom_was_false_seqnum` in `OmegaP3Semantic.lean`), permanently
documenting that the shipped axiom was refutable.

Resulting axiom inventory for `OmegaP3Semantic`: exactly **one** user
axiom, `compute_hash_collision_resistant` (idealised hash injectivity —
satisfiable because `compute_hash` is opaque; VCVio game-based reduction is
the planned replacement, see `../VCVIO_MIGRATION.md`). Earlier versions of
this document under-counted the user axioms by omitting
`canonicalBytes_injective` from the posture row; that omission is corrected
by the axiom's removal.
