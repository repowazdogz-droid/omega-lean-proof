# omega-lean-proof

Public [Lake](https://github.com/leanprover/lean4) package for the **OMEGA Protocol v1.3** Lean 4 scaffolding: [`OmegaProof.lean`](./OmegaProof.lean).

**Project site:** [omegaprotocol.org](https://omegaprotocol.org/)  
**Formal proof page:** [omegaprotocol.org/omega/formal-proof/](https://omegaprotocol.org/omega/formal-proof/)

Licensed under the [MIT License](./LICENSE).

## Verification status (2026-06-12)

Current machine-checked status. This supersedes the dated receipts further down (which reference the earlier `v4.18.0` pin and a since-removed axiom). Every claim has a command — run the command rather than trust the prose.

**Toolchain.** Lean 4 `v4.27.0`, pinned in [`lean-toolchain`](./lean-toolchain). No external Lake dependencies; no Mathlib (no `import Mathlib` in any shipped module).

```bash
cat lean-toolchain              # leanprover/lean4:v4.27.0
grep -c require lakefile.lean   # 0
```

**Build.** Green, 15 jobs.

```bash
lake build                      # Build completed successfully (15 jobs)
```

**`sorry` in shipped code: 0.** No shipped Lake root contains a proof-term `sorry`. The only real `sorry` left in the repo is one `OPEN` marker in the non-root `OmegaV15.lean` draft (see Known open items); a clean `lake build` emits no `uses 'sorry'` warning.

```bash
lake build 2>&1 | grep -c "uses 'sorry'"   # 0
```

**Axioms: zero user-declared axioms.** No `axiom` is declared in any shipped root. One `opaque` declaration, `compute_hash` (a SHA-256 placeholder, uninterpreted — not an axiom), is the only uninterpreted constant. The cryptographic assumption behind tamper-evidence (hash injectivity / collision resistance) is carried as an **explicit theorem hypothesis** (`hash_cr`), discharged at each call site, rather than as a global axiom; the axiom-free constructive core is `tamper_implies_collision`. Every shipped theorem depends only on Lean's standard built-ins `propext`, `Classical.choice`, `Quot.sound`.

```bash
grep -rn '^[[:space:]]*axiom ' *.lean OmegaJCS/*.lean   # (no output: zero axioms)
cat > /tmp/ax.lean <<'EOF'
import OmegaJCS.Roundtrip
import OmegaP3Semantic
#print axioms OmegaJCS.decode_encode             -- [propext, Classical.choice, Quot.sound]
#print axioms OmegaJCS.jcsEncode_injective       -- [propext, Classical.choice, Quot.sound]
#print axioms OmegaP3Semantic.tamper_detection   -- [propext, Classical.choice, Quot.sound]
#print axioms OmegaP3Semantic.tamper_implies_collision
EOF
lake env lean /tmp/ax.lean
```

**Key theorems.**

| Theorem | File | What is proven |
|---|---|---|
| `OmegaJCS.decode_encode` | [`OmegaJCS/Roundtrip.lean`](./OmegaJCS/Roundtrip.lean) | Decoding the canonical (JCS) encoding of a well-formed JSON value returns it: `jcsDecode (jcsEncode v) = some v`. |
| `OmegaJCS.jcsEncode_injective` | [`OmegaJCS/Roundtrip.lean`](./OmegaJCS/Roundtrip.lean) | Distinct well-formed JSON values have distinct canonical encodings. |
| `OmegaP3Semantic.tamper_implies_collision` | [`OmegaP3Semantic.lean`](./OmegaP3Semantic.lean) | Altering a payload in a hash-linked record chain forces a `compute_hash` collision (axiom-free). |
| `OmegaP3Semantic.tamper_detection` | [`OmegaP3Semantic.lean`](./OmegaP3Semantic.lean) | Under an explicit hash-injectivity hypothesis, a tampered chain cannot satisfy `P3_Traceability`. |
| `OmegaHashChain.omega_chain_append_only` | [`OmegaHashChain.lean`](./OmegaHashChain.lean) | Appending a well-formed record at the tip leaves all prior entries unchanged. |

**Known open items.** `OmegaV15.lean` is a parallel v1.5 draft, **not** a Lake root. It carries one `OPEN [O2]` obligation, `p6_no_coalition_escape`, which is **false as written**: the premise `P6_AgencyBoundary_Holds` admits the atomic-single-actor mode that the conclusion excludes, and the coupling hypothesis ranges over variables independent of the boundary. The refutation is machine-checked in [`probes/O2Counterexample.lean`](./probes/O2Counterexample.lean) (`o2_premise_too_weak`, axiom-free); a corrected statement is future work. Development scratch probes were archived to `archived/lean-proof-scratch-2026-06-12.tar.zst` and removed from the tree.

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
| [`OmegaP3Semantic.lean`](./OmegaP3Semantic.lean) | `P3_Traceability` as a concrete predicate over `List Record` (well-formedness, hash linkage, seq-num contiguity), a verified canonical-encoding decoder with proven injectivity on WF records, a real tamper-detection proof, and two machine-checked counterexample theorems documenting the removed `canonicalBytes_injective` axiom | 0 | `compute_hash` (SHA-256 placeholder, `opaque`), `compute_hash_collision_resistant` (idealised collision resistance) — the sole user axiom |
| [`OmegaP1Governance.lean`](./OmegaP1Governance.lean) | `P1_Governance` as a concrete predicate over the contract-and-agent presence pair; 2 theorems on contract and agent necessity | 0 | none |
| [`FailureProtocol.lean`](./FailureProtocol.lean) | `FailureAction` inductive with six cases (`retry`, `dead_letter`, `escalate_first`, `escalate_second`, `kill`, `circuit_breaker`); 2 theorems linking retry-limit overflow to escalation and retries-with-success to monitoring | 1 | none |

`OmegaProof.lean`, `OmegaV14.lean`, and `OmegaP1Governance.lean` are axiom-free at the user level — they rely only on Lean's standard built-ins (`Eq.refl` / `propext` and friends introduced implicitly by tactics) and use only `Prop`, `∧`, `¬`, `fun`, and `Iff`. `OmegaP3Semantic.lean` is in a deliberately different posture: it models a concrete hash chain and introduces two named declarations — `compute_hash` (an `opaque` SHA-256 placeholder, to be replaced by VCVio's verified implementation — see *Next step* below) and `compute_hash_collision_resistant` (idealised collision resistance, the **sole user axiom** in the package). Only `compute_hash_collision_resistant` propagates into theorem dependencies (via `tamper_detection`); the encoding-injectivity theorem `canonicalBytes_injective_wf` and the decoder roundtrip `decode_encode` depend on no user axioms. `FailureProtocol.lean` retains one `sorry` by design on `retries_with_success_requires_monitoring`: the proof obligation is a design-choice axiom that excessive-retries-with-success implies an operational monitoring requirement, which cannot be derived from first principles and is left as an explicit gap.

> **Soundness fix (2026-06-09):** the former second axiom
> `canonicalBytes_injective` (unconditional injectivity of the canonical
> encoding) was found to be **false in the model** — `seq_num : Nat` is
> truncated to 64 bits by `encodeSeqNum`, and `encodePrevHash` carries no
> length delimiter, so distinct records could encode identically. The axiom
> was removed and replaced by the proven theorem
> `canonicalBytes_injective_wf`, restricted to well-formed records
> (`Record.WF`: `seq_num < 2^64`, 32-byte `prev_hash`), with `WF` threaded
> through `P3_Traceability`. Both counterexamples are machine-checked and
> kept as the negative regression theorems `old_axiom_was_false` and
> `old_axiom_was_false_seqnum`. See
> [`docs/ASSURANCE_BOUNDARY.md`](./docs/ASSURANCE_BOUNDARY.md) changelog.

## Verification status (May 2026, post-toolchain-bump receipt)

| Item | Status |
|------|--------|
| **Toolchain** | `leanprover/lean4:v4.18.0` (pinned in [`lean-toolchain`](./lean-toolchain)) |
| **`lake build`** | All five targets build cleanly. Only warning emitted is the expected `declaration uses 'sorry'` on `FailureProtocol.retries_with_success_requires_monitoring`. |
| **Kernel typecheck (build-time)** | Lean's elaborator runs the kernel on every theorem at compile time. Clean `lake build` confirms every non-`sorry` proof typechecks. |
| **`#print axioms` (per-target spot-checks)** | Recorded below; matches the declared axiom posture for every target. |
| **SafeVerify replay** | **Pass** (2026-05-19): SafeVerify `main` @ Lean v4.27.0 on `OmegaProof.olean`, `OmegaV14.olean` (see formal-proof page). |
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

'OmegaP3Semantic.canonicalBytes_injective_wf' depends on axioms: [propext, Classical.choice, Quot.sound]
'OmegaP3Semantic.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
'OmegaP3Semantic.decodeSeqNum_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
'OmegaP3Semantic.tamper_detection' depends on axioms: [propext,
 Classical.choice,
 OmegaP3Semantic.compute_hash_collision_resistant,
 Quot.sound]
'OmegaP3Semantic.chain_integrity_extends' depends on axioms: [propext]
'OmegaP3Semantic.old_axiom_was_false' depends on axioms: [propext, Quot.sound]
'OmegaP3Semantic.old_axiom_was_false_seqnum' depends on axioms: [propext, Quot.sound]
'OmegaP3Semantic.chain_no_gaps' depends on axioms: [propext]

'OmegaP1Governance.governance_requires_contract' does not depend on any axioms
'OmegaP1Governance.governance_requires_agent'    does not depend on any axioms

'retries_exceed_limit_implies_escalation'    does not depend on any axioms
'retries_with_success_requires_monitoring'   depends on axioms: [sorryAx]
```

`propext`, `Classical.choice`, and `Quot.sound` are Lean built-ins (the latter two enter via core `List`/`Array`/`ByteArray` lemmas used by the decoder proofs), not user-declared axioms; `sorryAx` is Lean's marker for the single declared `sorry` in `FailureProtocol`; `compute_hash_collision_resistant` is the **sole** named user axiom in the package and only enters `tamper_detection` (and its computational stub). `canonicalBytes_injective_wf` and `decode_encode` — the proven replacements for the removed `canonicalBytes_injective` axiom — depend on no user axioms, and the negative regression theorems `old_axiom_was_false` / `old_axiom_was_false_seqnum` are kernel-checked refutations of the old axiom's statement.

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
#print axioms OmegaP3Semantic.canonicalBytes_injective_wf
#print axioms OmegaP3Semantic.decode_encode
#print axioms OmegaP3Semantic.tamper_detection
#print axioms OmegaP3Semantic.chain_integrity_extends
#print axioms OmegaP3Semantic.old_axiom_was_false
#print axioms OmegaP3Semantic.chain_no_gaps
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
