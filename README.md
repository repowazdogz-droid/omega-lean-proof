# omega-lean-proof

Public [Lake](https://github.com/leanprover/lean4) package for the **OMEGA Protocol v1.3** Lean 4 scaffolding: [`OmegaProof.lean`](./OmegaProof.lean).

**Project site:** [omegaprotocol.org](https://omegaprotocol.org/)  
**Formal proof page:** [omegaprotocol.org/omega/formal-proof/](https://omegaprotocol.org/omega/formal-proof/)

Licensed under the [MIT License](./LICENSE).

## What is formalised?

`Governed` is a right-nested conjunction of **seventeen** independent `Prop` atoms:

- the v1.2 twelvefold bundle (P1 through P6 family, including P4M, P4T, P5E, P6A, P6L, PCF),
- **P10** Competence Attestation, **P11** Expectation Update Integrity, **P12** Semantic Integrity Validation,
- honest limits **FAH** (Accountability Horizon) and **FAA** (Attestation Authority Integrity) as explicit conjuncts.

Theorems cover necessity projections, joint sufficiency, contrapositive absence lemmas, definitional `Iff.rfl`, and an explicit packaging theorem. The file uses only `Prop`, `∧`, `¬`, `fun`, and `Iff`: **no Mathlib**, **no `sorry`**, **no user-declared axioms**.

A byte-identical copy of the legacy twelve-primitive site file is preserved under [`v12-source/omega_v12_lean4_proof.lean`](./v12-source/omega_v12_lean4_proof.lean) (not built by Lake).

## SymPy failure-mode necessity (v1.3 schema primitives)

[`documents/necessity_all15.py`](./documents/necessity_all15.py) — SHA256 `0ab3a965ca7a90385c3b6cd9cac54829f196c5e155bc2092a4d72995a747c801` (verified `5e7f7b43` encoding + hard shared-flipped-literal guard).

Each failure mode \(F_i\) is a formula over **domain variables only** (never naming \(P_i\); `g2`: primitive name not in `symbols(F_i)`). Necessity per primitive: \(F_i\) satisfiable; \(F_i \land \neg P_i\) satisfiable; \(F_i \land P_i\) unsatisfiable. Hard guard: no shared domain atom may be forced to opposite polarity in \(F_i\) and \(P_i\).

| Category | Primitives | Status |
|----------|------------|--------|
| **Machine-checked** | P1, P3, P4, P5, P5E, P6, P10, P11, P12 | CLEAN PASS (domain-grounded; hard guard PASS) |
| **Design rationale** | P2, P4M, P4T, P6A, P6L | AWKWARD PASS (propositional proxy only) |
| **Resistant** | PCF | RESISTANT (tag; proxy passes structural slice) |

```bash
pip install sympy
python3 documents/necessity_all15.py
# Summary: 9 CLEAN necessity proven, 5 AWKWARD (proxy, passes), 1 RESISTANT
# HARD GUARD: all 9 CLEAN primitives PASS (no shared flipped literal)
```

This is **not** Lean conjunction necessity (`Governed → P_i`). It is **not** deployment attestation. Six primitives are design claims supported by the adversarial registry until quantitative/temporal formalisation lands. **No** committed check establishes sufficiency, independence, or irreducibility for all fifteen.

See [`docs/ASSURANCE_BOUNDARY.md`](./docs/ASSURANCE_BOUNDARY.md) (aligned with [formal-proof page](https://omegaprotocol.org/omega/formal-proof/)).

## Verified artifacts (May 2026)

| File | Coverage | `sorry` in proof | User axioms (beyond Lean built-ins) |
|------|----------|------------------|--------------------------------------|
| [`OmegaProof.lean`](./OmegaProof.lean) (v1.3) | 17-conjunct `Governed`, 37 theorems: necessity projections, joint sufficiency, contrapositive absence, biconditional, packaging | 0 | none |
| [`OmegaV14.lean`](./OmegaV14.lean) (v1.4.1) | 22-conjunct `Governed` extending v1.3 with `P2_DAG`, `P6_AtomicAgency`, `P1_Freshness`, `P4T_EnvInvariant`, `P_ChainIntegrity`; 13 theorems on the same pattern | 0 | none |
| [`OmegaP3Semantic.lean`](./OmegaP3Semantic.lean) | `P3_Traceability` as a concrete predicate over `List Record` with hash linkage, seq-num contiguity, and a real tamper-detection proof; 5 theorems | 0 | `compute_hash` (opaque SHA-256 placeholder), `canonicalBytes_injective` (canonical-byte-encoding injectivity), `compute_hash_collision_resistant` (collision resistance) |
| [`OmegaP1Governance.lean`](./OmegaP1Governance.lean) | `P1_Governance` as a concrete predicate over the contract-and-agent presence pair; 2 theorems on contract and agent necessity | 0 | none |
| [`FailureProtocol.lean`](./FailureProtocol.lean) | `FailureAction` inductive with six cases (`retry`, `dead_letter`, `escalate_first`, `escalate_second`, `kill`, `circuit_breaker`); 1 theorem linking retry-limit overflow to escalation. The retries-with-success monitoring rule is a spec choice in [`failure-protocol.md`](./failure-protocol.md), carried in Lean only as a `def retries_with_success`, not a theorem | 0 | none |

`OmegaProof.lean`, `OmegaV14.lean`, and `OmegaP1Governance.lean` are axiom-free at the user level — they rely only on Lean's standard built-ins (`Eq.refl` / `propext` and friends introduced implicitly by tactics) and use only `Prop`, `∧`, `¬`, `fun`, and `Iff`. `OmegaP3Semantic.lean` is in a deliberately different posture: it models a concrete hash chain and introduces three named declarations — `compute_hash` (an `opaque` SHA-256 placeholder, to be replaced by VCVio's verified implementation — see *Next step* below), `canonicalBytes_injective` (canonical-byte-encoding injectivity, an explicitly declared assumption), and `compute_hash_collision_resistant` (collision resistance, a standard cryptographic assumption). Both `canonicalBytes_injective` and `compute_hash_collision_resistant` propagate into theorem dependencies via `tamper_detection`, so that theorem depends on `[propext, canonicalBytes_injective, compute_hash_collision_resistant]`; the other four theorems in that file depend only on `propext`. `FailureProtocol.lean` is now `sorry`-free: the earlier deliberate `sorry` on `retries_with_success_requires_monitoring` has been retired by removing that theorem entirely. The operational rule (excessive retries with success implies a monitoring requirement) is not derivable from the retry arithmetic, so it lives where it belongs, in the spec [`failure-protocol.md`](./failure-protocol.md); Lean keeps only a `def retries_with_success` to give the rule a name. All seven shipped roots are `sorry`-free.

## Verification status (May 2026, post-toolchain-bump receipt)

| Item | Status |
|------|--------|
| **Toolchain** | `leanprover/lean4:v4.27.0` (pinned in [`lean-toolchain`](./lean-toolchain)). Bumped from v4.18.0 on 2026-05-19 to restore SafeVerify replay; see [`Docs/lean-verification-upgrade-2026-05-19.md`](../Docs/lean-verification-upgrade-2026-05-19.md). (Sibling proof repos pin their own toolchains: PolicyWitness is on v4.27.0, the honest-layer cross-layer witness on v4.30.0.) |
| **`lake build`** | All shipped roots build cleanly. No `declaration uses 'sorry'` warning is emitted: the tree is `sorry`-free. |
| **Kernel typecheck (build-time)** | Lean's elaborator runs the kernel on every theorem at compile time. Clean `lake build` confirms every non-`sorry` proof typechecks. |
| **`#print axioms` (per-target spot-checks)** | Recorded below; matches the declared axiom posture for every target. |
| **SafeVerify replay** | **Pass** (2026-05-19): SafeVerify `main` @ Lean v4.27.0 on `OmegaProof.olean`, `OmegaV14.olean` (see formal-proof page). |
| **`sorry`** | None. The earlier deliberate `sorry` was retired by removing `retries_with_success_requires_monitoring`; all seven shipped roots are `sorry`-free. (`OmegaV15.lean`, the parallel v1.5 work-in-progress, is **not** a Lake root and still carries one open `sorry`.) |

### Recorded `#print axioms` receipts

```
'p1_necessary' does not depend on any axioms
'all_governed_conjuncts_sufficient' does not depend on any axioms
'p1_absent_governed_false' does not depend on any axioms
'governed_iff_all_conjuncts' does not depend on any axioms
'authorisation_condition' does not depend on any axioms

'OmegaV14.p2_dag_necessary' does not depend on any axioms
'OmegaV14.all_twentytwo_conjuncts_sufficient' does not depend on any axioms
'OmegaV14.governed_iff_all_conjuncts' does not depend on any axioms
'OmegaV14.governed_fails_without_p2_dag' does not depend on any axioms

'OmegaP3Semantic.linked_from_append_single' depends on axioms: [propext]
'OmegaP3Semantic.chain_integrity_extends'  depends on axioms: [propext]
'OmegaP3Semantic.chain_monotonicity'       depends on axioms: [propext]
'OmegaP3Semantic.tamper_detection'         depends on axioms: [propext, OmegaP3Semantic.canonicalBytes_injective, OmegaP3Semantic.compute_hash_collision_resistant]
'OmegaP3Semantic.chain_no_gaps' does not depend on any axioms

'OmegaP1Governance.governance_requires_contract' does not depend on any axioms
'OmegaP1Governance.governance_requires_agent'    does not depend on any axioms

'retries_exceed_limit_implies_escalation'    does not depend on any axioms
```

`propext` is a Lean built-in, not a user-declared axiom. The package declares exactly two named user axioms, both in `OmegaP3Semantic.lean` and both flowing only into `tamper_detection`: `canonicalBytes_injective` (canonical-byte-encoding injectivity) and `compute_hash_collision_resistant` (SHA-256 collision resistance). There is no `sorryAx` anywhere in the shipped roots: the earlier deliberate `sorry` was retired by removing `retries_with_success_requires_monitoring`, and `#print axioms` on it now reports an unknown constant rather than `[sorryAx]`.

## Reproduce locally

```bash
git clone https://github.com/repowazdogz-droid/omega-lean-proof.git
cd omega-lean-proof
lake build
```

Reproduce the `#print axioms` receipts:

```bash
cat > /tmp/axioms.lean <<'EOF'
import OmegaProof
import OmegaV14
import OmegaP3Semantic
import OmegaP1Governance
import FailureProtocol

#print axioms p1_necessary
#print axioms OmegaV14.p2_dag_necessary
#print axioms OmegaP3Semantic.tamper_detection
#print axioms OmegaP1Governance.governance_requires_contract
#print axioms retries_exceed_limit_implies_escalation
EOF
lake env lean /tmp/axioms.lean
```

## SafeVerify status (passed)

Earlier verification rounds used [SafeVerify](https://github.com/GasStationManager/SafeVerify) `Environment.replay` on a built `.olean`, on the `minif2f-kimina-check` branch pinned to Lean v4.15.0. An interim bump to v4.18.0 (for the VCVio SHA-256 substitution work) had lost binary compatibility with the available SafeVerify branches, which left replay deferred for a time. That gap is now closed: on 2026-05-19 the toolchain was bumped to **v4.27.0**, and SafeVerify `main` @ Lean v4.27.0 replayed `OmegaProof.olean` (38 declarations) and `OmegaV14.olean` (14 declarations) with allowed axioms only, **pass**. See [`Docs/lean-verification-upgrade-2026-05-19.md`](../Docs/lean-verification-upgrade-2026-05-19.md) for the bump receipt.

`lean4lean` @ v4.29.0 was evaluated first as the preferred verifier but segfaults / hits kernel deep-recursion on `OmegaProof`, so attestation uses SafeVerify at v4.27.0.

The verification stack is therefore: clean `lake build` under Lean v4.27.0 (which exercises Lean's kernel on every theorem during elaboration), plus the `#print axioms` receipts above, plus the external SafeVerify replay.

## Toolchain and Mathlib

- **Mathlib:** not required for this proof package itself (no `import Mathlib`). Mathlib is pulled transitively only via the VCVio dependency, which is required at lake-level but not imported by any of the current source files.
- The `v4.27.0` pin matches the [`leanprover-community/mathlib4`](https://github.com/leanprover-community/mathlib4) tag **v4.27.0** if you extend the package later.

## Next step

The next major step is to replace the `compute_hash` opaque declaration in `OmegaP3Semantic.lean` with the verified SHA-256 implementation from [VCVio](https://github.com/dtumad/VCV-io). VCVio's `LibSodium/SHA2.lean` slot is upstream-empty at v4.27.0; a future commit will wire it through (or via a local FFI module) once that slot is populated. After the substitution, `OmegaP3Semantic` will rest on one fewer named declaration; only `compute_hash_collision_resistant` (collision resistance) remains as the irreducible cryptographic assumption.

## Legacy path on the public site

The canonical downloadable v1.2 artifact remains at  
`https://omegaprotocol.org/omega/formal-proof/omega_v12_lean4_proof.lean`  
(this repository's `v12-source/` copy matches that file for provenance).
