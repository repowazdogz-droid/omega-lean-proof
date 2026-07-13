# OMEGA polyglot bindings — ATTESTATION MANIFEST

> **STATUS: PUBLISHED — PUBLIC ARTIFACT.** This manifest, the binding sources and the
> receipts it references are public on `main` (merged in PR #1). The `.olean` build
> artifacts are not committed: CI rebuilds them from a clean checkout on every push and
> re-derives their digests. The earlier HELD / DO-NOT-PUBLISH status is superseded and
> no longer applies.

Run date (UTC): **2026-06-30T06:54Z**
Produced by: SafeVerify pipeline (Lean kernel) + per-paradigm tool re-run
(correspondence). Lane was strictly *binding files + verification pipeline*;
nothing shipped was modified.

## Provenance

| Item | Value |
|------|-------|
| Repo | `~/Omega/lean-proof` (github.com/repowazdogz-droid/omega-lean-proof) |
| Shipped tree HEAD | `6aa9008db9789a2c29989d4a84f50445905572d4` |
| Binding files | **tracked and committed on `main`** (`OmegaP*Binding.lean`, merged in PR #1); intentionally **not** in the Lake roots, and independently rebuilt and verified from a clean checkout by the reproducibility workflow on every push |
| In-project Lean | `v4.27.0` (pinned by `lean-toolchain`; global elan default is 4.31.0 and is NOT what ran) |
| SafeVerify binary | `.cache/SafeVerify/.lake/build/bin/safe_verify`, runs on Lean **v4.27.0**, sha256 `104baa73…56d15f` |
| Allowlist (hardcoded in SafeVerify) | `{propext, Quot.sound, Classical.choice}` |

**What "attested commit" means here:** the shipped olean base is HEAD `6aa9008`
(`lake build`, 16 jobs, clean). The bindings themselves are **additive untracked
files** compiled against that base. They are NOT yet committed and NOT Lake roots,
so there is no attested *commit* for the bindings — only an attested *run* (this
manifest) against the `6aa9008` olean base. See "Path-to-roots" below.

---

## A. Lean bindings — KERNEL-ATTESTED via SafeVerify (instantiation)

Each binding instantiates its conjunct's `Prop` slot in the shipped
`OmegaV14.all_twentytwo_conjuncts_sufficient` and discharges it in-kernel.
Attestation = SafeVerify **self-replay** (`safe_verify f.olean f.olean`,
`LEAN_PATH=.lake/build/lib/lean`): every declaration is kernel-typechecked on a
rebuilt expression tree and every theorem's axiom set is checked ⊆ allowlist.

| Binding | Conjunct | safe_verify | decls / fails | `#print axioms` | olean sha256 |
|---------|----------|-------------|---------------|-----------------|--------------|
| OmegaP6ABinding | P6A Aggregate Materiality | **PASS** | 49 / 0 | **none** (zero-axiom) | `95b23e03…a8a9fc` |
| OmegaP4MBinding | P4M Materiality Binding | **PASS** | 37 / 0 | **none** | `d81c9038…15a429` |
| OmegaP6AtomicBinding | P6 Atomic Agency | **PASS** | 41 / 0 | **none** | `1431a5ba…4198d2` |
| OmegaP12Binding | P12 Semantic Integrity | **PASS** | 31 / 0 | **none** | `7cf856c9…00febe` |
| OmegaP2DAGBinding | P2 DAG (acyclicity) | **PASS** | 65 / 0 | **none** | `d4c2f2e6…c2c634` |
| OmegaP4TBinding | P4T Env Invariant | **PASS** | 37 / 0 | **none** | `a1283755…ac7966` |
| OmegaP6LBinding | P6L Liability Threshold | **PASS** | 43 / 0 | **none** | `28765027…0496a8d` |

All seven report **"does not depend on any axioms"** for every theorem — stronger
than the SafeVerify allowlist requires (zero ⊆ {propext, Quot.sound,
Classical.choice}). The explicitly-requested five (P6A, P4M, P6_Atomic, P12,
P2_DAG) are attested; P4T and P6L are the same operation and are attested too.

Receipts: `attested/receipts/<Binding>.json` (full per-declaration outcomes).
Oleans: `attested/oleans/<Binding>.olean`.

Trust base: **Lean 4 v4.27.0 kernel, zero user axioms.** This is the strongest
rung — a real proof object exists and is kernel-checked, and it plugs into the
shipped bundle theorem.

---

## B. TLA+ / CryptoVerif / Z3 — REPRODUCIBLE-VERIFICATION RECORDS (correspondence)

These are NOT kernel artifacts and **cannot go through SafeVerify** (it is
Lean-only). Each is a documented *correspondence* to its Lean atom — "this is what
the conjunct means, machine-checked in its proper paradigm" — **no proof object
crosses to the Lean `OmegaV14.Governed` slot.** Re-run live on the date above;
logs in `attested/correspondence/`.

### TLA+ / TLC 2.19 (Java 17) — model-checked, bounded
exit 12 = invariant violated (intended for witness/non-vacuity); exit 0 = holds.

| Run | cfg | Result | States (distinct) / depth | log |
|-----|-----|--------|---------------------------|-----|
| P1_Freshness weak | weak | Freshness **VIOLATED** (witness) | 92 877 | tla_p1_weak.log |
| P1_Freshness repaired | repaired | **HOLDS** (no error) | 2 731 676 / depth 302 | tla_p1_repaired.log |
| P1_Freshness non-vacuity | nonvacuity | NoFreshAccept VIOLATED (intended) | 303 | tla_p1_nonvacuity.log |
| P5 Confirmation weak | weak | Ordering **VIOLATED** (witness) | 3 | tla_p5_weak.log |
| P5 Confirmation repaired | repaired | **HOLDS** | 3 | tla_p5_repaired.log |
| P5 Confirmation non-vacuity | nonvacuity | NoConfirmedExec VIOLATED (intended) | 3 | tla_p5_nonvacuity.log |
| P11 (temporal half) weak | weak | UpdateIntegrity **VIOLATED** (witness) | 4 | tla_p11_weak.log |
| P11 (temporal half) repaired | repaired | **HOLDS** | 120 | tla_p11_repaired.log |
| P11 (temporal half) non-vacuity | nonvacuity | NoValidUpdate VIOLATED (intended) | 4 | tla_p11_nonvacuity.log |

Trust base: TLC 2.19 + temporal-model fidelity (discrete 1-second ticks) +
**bounded** state space (exhaustive within the bound only). Discrete time, not
dense/timed-automata. Probabilistic fingerprinting (collision prob ≈ 3e-11).

### CryptoVerif 2.12 — verified under a NAMED computational assumption
| File | Property | Result | Assumption |
|------|----------|--------|-----------|
| PChainIntegrity_cr.cv | tamperAccepted ⇒ false | **All queries proved** up to `Phash` | collision-resistance |
| P5E_attestation.cv | executed ⇒ approved | **All queries proved** up to `Psign` | EUF-CMA |
| P5E_attestation_weak.cv | (executor skips verify) | **Could not prove** (witness) | — |
| P11link_unforgeable.cv | linkAccepted ⇒ linkIssued | **All queries proved** up to `Psign` | EUF-CMA |
| P11link_unforgeable_weak.cv | (verifier skips link check) | **Could not prove** (witness) | — |

Trust base: CryptoVerif 2.12 + **named hardness assumption (assumed, not proved)**
+ protocol-model fidelity. Deliberately NOT axiom-free — that is the correct shape
for a cryptographic result. P11 is hybrid: temporal half (TLA+) + crypto half here.

### Z3 / SMT (z3 4.16.0) — sound within encoding
| Check | Result | log |
|-------|--------|-----|
| P10 weak gate admits under-competent | **SAT** (witness, expected) | z3_p10_competence.log |
| P10 repaired gate blocks it | **UNSAT** (expected) | z3_p10_competence.log |
| P10 competent agent admissible | **SAT** (non-vacuity, expected) | z3_p10_competence.log |

Trust base: Z3 solver + linear-integer encoding (SAT/UNSAT sound for the encoding;
a wrong encoding ⇒ a wrong verdict). Correspondence, not instantiation.

---

## Honest boundary (load-bearing — keep on any derived copy)

1. **Two different things are claimed.** Section A = kernel instantiation (Lean
   proof object, zero-axiom, plugs into the shipped bundle). Section B =
   documented correspondence (the tool checks a model of the conjunct; nothing
   crosses to the Lean atom). A is strictly stronger than B.
2. **CryptoVerif rests on assumed-not-proved named assumptions** (CR / EUF-CMA).
3. **Model-level only.** No claim any deployed system matches these models.
4. **Bundle status unchanged:** "fully ACCOUNTED-FOR ≠ verified." This run
   attests the *bindings*, raising 13 conjuncts from "bound on paper" to
   "bound + freshly machine-checked/attested." It does not make OMEGA "verified."

## Path-to-roots (PROPOSAL — not executed, needs its own review)

To make the Lean bindings attested at a *committed* surface (not just this run),
they would become Lake roots. Per `lean-proof/CLAUDE.md` session rule #2, adding
roots changes the public surface and needs a scoped review — **not forced here.**
Proposed (additive, no shipped root touched), as a separate `lean_lib`:

```lean
lean_lib OmegaBindings where
  srcDir := "."
  roots := #[`OmegaP6ABinding, `OmegaP4MBinding, `OmegaP6AtomicBinding,
             `OmegaP12Binding, `OmegaP2DAGBinding, `OmegaP4TBinding, `OmegaP6LBinding]
```

No lakefile *dependency* change is required: bindings import only `OmegaV14`
(already a shipped root); the package is dependency-free (no VCVio, no Mathlib).
This change is left for the user to approve.

## Reproduce
`bash attested/reproduce.sh` (rebuilds oleans, re-runs SafeVerify + all
correspondence tools).
