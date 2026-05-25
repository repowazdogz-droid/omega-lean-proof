# omega-lean-proof

**Layer:** Doctrine

## Position in OMEGA Lab

Formal predicate scaffolding — not deployment attestation. Lean proves statements about *definitions*, not that production systems satisfy them. See [failure-protocol.md](./failure-protocol.md). Implementation status: [omega-contracts PRIMITIVE_MAP](https://github.com/repowazdogz-droid/omega-contracts/blob/main/docs/PRIMITIVE_MAP.md) (Lean = conceptual/doctrine). Assurance boundary: [docs/ASSURANCE_BOUNDARY.md](./docs/ASSURANCE_BOUNDARY.md).

Public [Lake](https://github.com/leanprover/lean4) package for the **OMEGA Protocol v1.3** Lean 4 scaffolding: [`OmegaProof.lean`](./OmegaProof.lean).

**Project site:** [omegaprotocol.org](https://omegaprotocol.org/)  
**Public doctrine page (scaffolding):** [omegaprotocol.org/omega/formal-proof/](https://omegaprotocol.org/omega/formal-proof/)

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
| [`FailureProtocol.lean`](./FailureProtocol.lean) | `FailureAction` inductive with six cases (`retry`, `dead_letter`, `escalate_first`, `escalate_second`, `kill`, `circuit_breaker`); one theorem linking retry-limit overflow under failed verification to escalation. The operational rule "excess retries with success → monitor" is intentionally kept in [`failure-protocol.md`](./failure-protocol.md) rather than encoded as a Lean theorem (no derivation from first principles is possible, and a definitional rename would carry no semantic content). | 0 | none |
| [`OmegaHashChain.lean`](./OmegaHashChain.lean) | Append-only hash chain lemmas over `OmegaP3Semantic.Record`; `omega_chain_append_only`, `valid_chain_extend` | 0 | none |
| [`OmegaGovernance.lean`](./OmegaGovernance.lean) | Decision-gravity partial order on `GovernanceLevel` (G1–G4); reflexivity, transitivity, antisymmetry | 0 | none |

`OmegaProof.lean`, `OmegaV14.lean`, and `OmegaP1Governance.lean` are axiom-free at the user level — they rely only on Lean's standard built-ins (`Eq.refl` / `propext` and friends introduced implicitly by tactics) and use only `Prop`, `∧`, `¬`, `fun`, and `Iff`. `OmegaP3Semantic.lean` is in a deliberately different posture: it models a concrete hash chain and introduces two named declarations — `compute_hash` (an `opaque` SHA-256 placeholder, to be replaced by VCVio's verified implementation — see *Next step* below) and `compute_hash_collision_resistant` (collision resistance, a standard cryptographic assumption). Only `compute_hash_collision_resistant` propagates into theorem dependencies (via `tamper_detection`); the other four theorems in that file depend only on `propext`. `FailureProtocol.lean` is `sorry`-free and axiom-free: it formalises only the retry-limit-plus-failed-verification escalation rule, which is a direct conjunction-introduction. The "excess retries with success → monitor" operational rule is documented in [`failure-protocol.md`](./failure-protocol.md); it is not derivable from the retry arithmetic and was previously a stated-with-`sorry` placeholder, which has been removed in favour of the markdown spec to avoid either a smuggled axiom or a definitionally vacuous theorem.

## Verification status (May 2026, post-toolchain-bump receipt)

| Item | Status |
|------|--------|
| **Toolchain** | `leanprover/lean4:v4.27.0` (pinned in [`lean-toolchain`](./lean-toolchain)) |
| **`lake build`** | All seven shipped targets build cleanly. No `declaration uses 'sorry'` warning in shipped roots. |
| **Kernel typecheck (build-time)** | Lean's elaborator runs the kernel on every theorem at compile time. Clean `lake build` confirms every non-`sorry` proof typechecks. |
| **`#print axioms` (per-target spot-checks)** | Recorded below; matches the declared axiom posture for every target. |
| **SafeVerify replay** | **Pass** (2026-05-19). [SafeVerify](https://github.com/GasStationManager/SafeVerify) `main` @ Lean v4.27.0 replays `OmegaProof.olean` (38 declarations) and `OmegaV14.olean` (14 declarations) with allowed axioms only. |
| **lean4lean** | **Not used for attestation.** lean4lean @ v4.29.0 segfaults (exit 139) / deep-recursion on `OmegaProof`; toolchain pinned to v4.27.0 for SafeVerify compatibility instead. |
| **`sorry` (shipped roots)** | None. `OmegaV15.lean` (parallel v1.5, not in Lake roots) retains one open `sorry`. |

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
```

`propext` is a Lean built-in, not a user-declared axiom; `compute_hash_collision_resistant` is the sole named user axiom in the package and only enters `tamper_detection`.

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

## SafeVerify status (2026-05-19)

[SafeVerify](https://github.com/GasStationManager/SafeVerify) `main` is pinned to Lean **v4.27.0**, matching this package's `lean-toolchain`.

Reproduce the external verifier replay:

```bash
cd lean-proof
lake build
lake env lean -o /tmp/OmegaProof.olean OmegaProof.lean
lake env lean -o /tmp/OmegaV14.olean OmegaV14.lean
# Build SafeVerify once (cached under lean-proof/.cache/SafeVerify)
cd .cache/SafeVerify && lake build safe_verify && cd ../..
.cache/SafeVerify/.lake/build/bin/safe_verify /tmp/OmegaProof.olean /tmp/OmegaProof.olean
.cache/SafeVerify/.lake/build/bin/safe_verify /tmp/OmegaV14.olean /tmp/OmegaV14.olean
```

Expected output: `SafeVerify check passed.` for both files.

**lean4lean** (Mario Carneiro, v4.29.0) was evaluated first per preference order but segfaulted / hit kernel deep-recursion on `OmegaProof`; attestation uses SafeVerify instead.

## Toolchain and Mathlib

- **Mathlib:** not required for shipped proof modules (no direct `import Mathlib`). Mathlib is pulled transitively via VCVio (lake-level dependency; build with `lake build VCVio` when probing crypto imports).
- The `v4.27.0` pin matches [SafeVerify `main`](https://github.com/GasStationManager/SafeVerify) and [`VCVio` v4.27.0](https://github.com/dtumad/VCV-io).

## Next step

The next major step is to replace the `compute_hash` opaque declaration in `OmegaP3Semantic.lean` with the verified SHA-256 implementation from [VCVio](https://github.com/dtumad/VCV-io). VCVio's `LibSodium/SHA2.lean` slot is upstream-empty at v4.18.0; a future commit will wire it through (or via a local FFI module) once that slot is populated. After the substitution, `OmegaP3Semantic` will rest on one fewer named declaration; only `compute_hash_collision_resistant` (collision resistance) remains as the irreducible cryptographic assumption.

## Legacy path on the public site

The canonical downloadable v1.2 artifact remains at  
`https://omegaprotocol.org/omega/formal-proof/omega_v12_lean4_proof.lean`  
(this repository's `v12-source/` copy matches that file for provenance).
