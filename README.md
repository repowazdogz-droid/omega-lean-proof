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

## Verified artifacts (May 2026)

| File | Coverage | `sorry` in proof | User axioms (beyond Lean built-ins) |
|------|----------|------------------|--------------------------------------|
| [`OmegaProof.lean`](./OmegaProof.lean) (v1.3) | 17-conjunct `Governed`, 37 theorems: necessity projections, joint sufficiency, contrapositive absence, biconditional, packaging | 0 | none |
| [`OmegaV14.lean`](./OmegaV14.lean) (v1.4.1) | 22-conjunct `Governed` extending v1.3 with `P2_DAG`, `P6_AtomicAgency`, `P1_Freshness`, `P4T_EnvInvariant`, `P_ChainIntegrity`; 13 theorems on the same pattern | 0 | none |
| [`OmegaP3Semantic.lean`](./OmegaP3Semantic.lean) | `P3_Traceability` as a concrete predicate over `List Record` with hash linkage, seq-num contiguity, and a real tamper-detection proof; 5 theorems | 0 | `compute_hash` (SHA-256 placeholder), `compute_hash_collision_resistant` (collision resistance) |
| [`OmegaP1Governance.lean`](./OmegaP1Governance.lean) | `P1_Governance` as a concrete predicate over the contract-and-agent presence pair; 2 theorems on contract and agent necessity | 0 | none |
| [`FailureProtocol.lean`](./FailureProtocol.lean) | `FailureAction` inductive with six cases (`retry`, `dead_letter`, `escalate_first`, `escalate_second`, `kill`, `circuit_breaker`); 2 theorems linking retry-limit overflow to escalation and retries-with-success to monitoring | 1 | none |

`OmegaProof.lean`, `OmegaV14.lean`, and `OmegaP1Governance.lean` are axiom-free at the user level — they rely only on Lean's standard built-ins (`Eq.refl` / `propext` and friends introduced implicitly by tactics) and use only `Prop`, `∧`, `¬`, `fun`, and `Iff`. `OmegaP3Semantic.lean` is in a deliberately different posture: it models a concrete hash chain and introduces two named declarations — `compute_hash` (an `opaque` SHA-256 placeholder, to be replaced by VCVio's verified implementation — see *Next step* below) and `compute_hash_collision_resistant` (collision resistance, a standard cryptographic assumption). Only `compute_hash_collision_resistant` propagates into theorem dependencies (via `tamper_detection`); the other four theorems in that file depend only on `propext`. `FailureProtocol.lean` retains one `sorry` by design on `retries_with_success_requires_monitoring`: the proof obligation is a design-choice axiom that excessive-retries-with-success implies an operational monitoring requirement, which cannot be derived from first principles and is left as an explicit gap.

## Verification status (May 2026, post-toolchain-bump receipt)

| Item | Status |
|------|--------|
| **Toolchain** | `leanprover/lean4:v4.18.0` (pinned in [`lean-toolchain`](./lean-toolchain)) |
| **`lake build`** | All five targets build cleanly. Only warning emitted is the expected `declaration uses 'sorry'` on `FailureProtocol.retries_with_success_requires_monitoring`. |
| **Kernel typecheck (build-time)** | Lean's elaborator runs the kernel on every theorem at compile time. Clean `lake build` confirms every non-`sorry` proof typechecks. |
| **`#print axioms` (per-target spot-checks)** | Recorded below; matches the declared axiom posture for every target. |
| **SafeVerify replay** | **Pending.** Upstream [GasStationManager/SafeVerify](https://github.com/GasStationManager/SafeVerify) skips Lean v4.18 entirely (toolchain history goes `v4.14 → v4.20 → v4.21`); both the legacy `minif2f-kimina-check` (4.15) and `v4.21` branches reject our 4.18 `.olean` files with `incompatible header`. A SafeVerify receipt will be added once an upstream branch targeting Lean v4.18, or a Lean toolchain bump matching an existing SafeVerify branch, lands. |
| **`sorry`** | One, by design, in `FailureProtocol.retries_with_success_requires_monitoring`. None elsewhere. |

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
'OmegaP3Semantic.tamper_detection'         depends on axioms: [OmegaP3Semantic.compute_hash_collision_resistant]
'OmegaP3Semantic.chain_no_gaps' does not depend on any axioms

'OmegaP1Governance.governance_requires_contract' does not depend on any axioms
'OmegaP1Governance.governance_requires_agent'    does not depend on any axioms

'retries_exceed_limit_implies_escalation'    does not depend on any axioms
'retries_with_success_requires_monitoring'   depends on axioms: [sorryAx]
```

`propext` is a Lean built-in, not a user-declared axiom; `sorryAx` is Lean's marker for the single declared `sorry`; `compute_hash_collision_resistant` is the sole named user axiom in the package and only enters `tamper_detection`.

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
#print axioms retries_with_success_requires_monitoring
EOF
lake env lean /tmp/axioms.lean
```

## SafeVerify status (deferred)

Earlier verification rounds used [SafeVerify](https://github.com/GasStationManager/SafeVerify) `Environment.replay` on a built `.olean`, on the `minif2f-kimina-check` branch pinned to Lean v4.15.0. The recent toolchain bump to v4.18.0 (required by VCVio for the SHA-256 substitution) lost binary compatibility with that SafeVerify branch, and upstream SafeVerify does not currently ship a v4.18-compatible branch. The available branches `minif2f-kimina-check` (v4.15) and `v4.21` both reject 4.18 oleans:

```
Replaying .../OmegaProof.olean
uncaught exception: failed to read file '...', incompatible header
```

Two paths forward are open, neither pursued in this commit:
1. Bump `lean-toolchain` to v4.21.0 and re-verify VCVio compatibility, allowing SafeVerify `v4.21` to replay the resulting oleans.
2. Wait for an upstream SafeVerify branch matching Lean v4.18 (or maintain a fork pinned to v4.18 + Mathlib v4.18).

In the interim, the verification stack is: clean `lake build` under Lean v4.18.0 (which exercises Lean's kernel on every theorem during elaboration) plus the `#print axioms` receipts above.

## Toolchain and Mathlib

- **Mathlib:** not required for this proof package itself (no `import Mathlib`). Mathlib is pulled transitively only via the VCVio dependency, which is required at lake-level but not imported by any of the current source files.
- The `v4.18.0` pin matches the [`leanprover-community/mathlib4`](https://github.com/leanprover-community/mathlib4) tag **v4.18.0** if you extend the package later.

## Next step

The next major step is to replace the `compute_hash` opaque declaration in `OmegaP3Semantic.lean` with the verified SHA-256 implementation from [VCVio](https://github.com/dtumad/VCV-io). VCVio's `LibSodium/SHA2.lean` slot is upstream-empty at v4.18.0; a future commit will wire it through (or via a local FFI module) once that slot is populated. After the substitution, `OmegaP3Semantic` will rest on one fewer named declaration; only `compute_hash_collision_resistant` (collision resistance) remains as the irreducible cryptographic assumption.

## Legacy path on the public site

The canonical downloadable v1.2 artifact remains at  
`https://omegaprotocol.org/omega/formal-proof/omega_v12_lean4_proof.lean`  
(this repository's `v12-source/` copy matches that file for provenance).
