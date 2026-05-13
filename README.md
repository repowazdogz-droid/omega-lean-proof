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
| [`OmegaP3Semantic.lean`](./OmegaP3Semantic.lean) | `P3_Traceability` as a concrete predicate over `List Record` with hash linkage, seq-num contiguity, and a real tamper-detection proof; 5 theorems | 0 | `compute_hash` (SHA-256 placeholder), `compute_hash_injective` (collision resistance) |
| [`FailureProtocol.lean`](./FailureProtocol.lean) | `FailureAction` inductive with six cases (`retry`, `dead_letter`, `escalate_first`, `escalate_second`, `kill`, `circuit_breaker`); 1 theorem statement linking retry-limit overflow to escalation | 1 (statement only; proof pending) | none |

`OmegaProof.lean` and `OmegaV14.lean` are axiom-free at the user level — they rely only on Lean's standard built-ins (`Eq.refl` / `propext` and friends introduced implicitly by tactics) and use only `Prop`, `∧`, `¬`, `fun`, and `Iff`. `OmegaP3Semantic.lean` is in a deliberately different posture: it models a concrete hash chain and introduces two named axioms — `compute_hash` (placeholder for SHA-256, to be replaced by VCVio's verified implementation — see *Next step* below) and `compute_hash_injective` (collision resistance, a standard cryptographic assumption). `FailureProtocol.lean` intentionally retains one `sorry` on a theorem statement that is provable but not yet proved.

## Verification status (April 2026)

| Item | Status |
|------|--------|
| **Toolchain** | `leanprover/lean4:v4.15.0` (pinned in [`lean-toolchain`](./lean-toolchain)) |
| **`lake build`** | Succeeds; no warnings from `OmegaProof.lean` |
| **Kernel replay** | `lake env lean -o … OmegaProof.lean` then [SafeVerify](https://github.com/GasStationManager/SafeVerify) `Environment.replay` on the resulting `.olean`: passed |
| **SafeVerify** | Branch `minif2f-kimina-check`, commit `577e953`, self-check on `.olean`: exit code 0, message `Finished with no errors.` |
| **Axioms (spot-check)** | `#print axioms` on representative theorems reported no axioms; replay listing showed empty axiom sets for those declarations |
| **`sorry`** | None |

**Caveat:** SafeVerify `main` tracks Lean **v4.27.0**; for this proof package use branch **`minif2f-kimina-check`** so the Lean version matches the `.olean` format.

## Reproduce locally

```bash
git clone https://github.com/repowazdogz-droid/omega-lean-proof.git
cd omega-lean-proof
lake build
```

Emit an object file (same Lean as the project):

```bash
lake env lean -o /tmp/omegaproof.olean OmegaProof.lean
```

Build SafeVerify on the **Lean 4.15** branch, then run the checker (this branch’s executable expects exactly two path arguments):

```bash
git clone https://github.com/GasStationManager/SafeVerify.git /tmp/SafeVerify
cd /tmp/SafeVerify
git fetch origin minif2f-kimina-check --depth 1
git checkout -B minif2f-kimina-check FETCH_HEAD
lake build
cd /tmp/SafeVerify && lake env ./.lake/build/bin/safe_verify /tmp/omegaproof.olean /tmp/omegaproof.olean
```

See the [SafeVerify README](https://github.com/GasStationManager/SafeVerify/blob/main/README.md) for full semantics (kernel replay, allowed axioms, partial/unsafe rules on other branches).

## Toolchain and Mathlib

- **Mathlib:** not required for this proof (no `import Mathlib`).
- The `v4.15.0` pin matches the `leanprover-community/mathlib4` tag **v4.15.0** if you extend the package later.

## Next step

The next major step is to replace the `compute_hash` axiom in `OmegaP3Semantic.lean` with the verified SHA-256 implementation from [VCVio](https://github.com/dtumad/VCV-io). VCVio targets newer Lean toolchains than v4.15, so this requires bumping `lean-toolchain` to a VCVio-supported version (currently exploring v4.18) and retargeting the SafeVerify branch to the matching Lean version. After the substitution, `OmegaP3Semantic` will rest on one fewer named axiom; only `compute_hash_injective` (collision resistance) remains as the irreducible cryptographic assumption.

## Legacy path on the public site

The canonical downloadable v1.2 artifact remains at  
`https://omegaprotocol.org/omega/formal-proof/omega_v12_lean4_proof.lean`  
(this repository’s `v12-source/` copy matches that file for provenance).
