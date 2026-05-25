# Assurance boundary — omega-lean-proof (Doctrine)

Lean artifacts are meaningful only **inside an explicit boundary**. `omega-lean-proof` formalises named predicates and lemmas over those definitions. It does not attest that production systems, records, or runtime gates satisfy those predicates.

---

## omega-lean-proof provides

| Capability | Mechanism |
| --- | --- |
| **Named doctrine predicates** | `Governed`, P-family atoms, hash-chain lemmas in shipped Lean roots |
| **Logical structure proofs** | Necessity, sufficiency, packaging theorems over the defined conjunctions |
| **Reproducible build receipts** | `lake build`, `#print axioms`, SafeVerify replay for selected targets |
| **Explicit axiom posture** | Crypto assumptions isolated (e.g. `compute_hash_collision_resistant`) |

---

## omega-lean-proof does NOT provide

| Non-guarantee | Implication |
| --- | --- |
| **Deployment attestation** | A clean Lean build does not prove a live system is governed |
| **Runtime enforcement** | No gate evaluator, blocker, or router is shipped from this repo |
| **Record population** | Lean exports are **not embedded** in `@omega-protocol/contracts` records today |
| **Production security proof** | Hash/tamper lemmas model definitions under stated crypto assumptions, not your infrastructure |
| **Operational completeness** | Some operational rules live in markdown (e.g. [`failure-protocol.md`](./failure-protocol.md)), not as theorems |
| **Compliance certification** | Formal predicates are not regulatory guarantees |

Lean proves properties of **definitions**. Integrators must not treat theorem names as evidence that a deployment satisfies them.

---

## Trusted computing base (TCB)

| Component | Assumed correct |
| --- | --- |
| **Lean 4 kernel + toolchain pin** | [`lean-toolchain`](./lean-toolchain) |
| **Shipped Lean roots** | Files built by Lake without `sorry` in shipped targets |
| **SafeVerify replay** | External verifier configuration when cited in README receipts |
| **Reader interpretation** | Distinction between scaffolding and deployment claims |

**Outside the TCB:** sibling protocol libraries, `@omega-protocol/contracts` composition, runtime gates, and external attestation of production behavior.

---

## Failure modes

| Mode | Description |
| --- | --- |
| **Doctrine → deployment gap** | System satisfies record shape but not Lean predicate instantiation |
| **Axiom smuggling via naming** | Strong theorem names read as production guarantees |
| **Placeholder crypto** | `compute_hash` opaque placeholder until verified implementation is wired |
| **Operational rule drift** | Markdown operational rules not mirrored in formal proofs |
| **Version skew** | Site/marketing language ahead of shipped Lean roots |

---

## Contracts integration

See [omega-contracts PRIMITIVE_MAP](https://github.com/repowazdogz-droid/omega-contracts/blob/main/docs/PRIMITIVE_MAP.md): Lean is **doctrine / conceptual** relative to record slots. See also [TRUST_STACK](https://github.com/repowazdogz-droid/omega-contracts/blob/main/docs/TRUST_STACK.md).
