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
/tmp/SafeVerify/.lake/build/bin/safe_verify /tmp/omegaproof.olean /tmp/omegaproof.olean
```

See the [SafeVerify README](https://github.com/GasStationManager/SafeVerify/blob/main/README.md) for full semantics (kernel replay, allowed axioms, partial/unsafe rules on other branches).

## Toolchain and Mathlib

- **Mathlib:** not required for this proof (no `import Mathlib`).
- The `v4.15.0` pin matches the `leanprover-community/mathlib4` tag **v4.15.0** if you extend the package later.

## Legacy path on the public site

The canonical downloadable v1.2 artifact remains at  
`https://omegaprotocol.org/omega/formal-proof/omega_v12_lean4_proof.lean`  
(this repository’s `v12-source/` copy matches that file for provenance).
