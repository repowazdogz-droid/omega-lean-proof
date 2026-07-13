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

**Build.** Green, 16 jobs.

```bash
lake build                      # Build completed successfully (16 jobs)
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
| [`OmegaP3Semantic.lean`](./OmegaP3Semantic.lean) | `P3_Traceability` as a concrete predicate over `List Record` (well-formedness, hash linkage, seq-num contiguity), a verified canonical-encoding decoder with proven injectivity on WF records, a real tamper-detection proof, and two machine-checked counterexample theorems documenting the removed `canonicalBytes_injective` axiom | 0 | **none** — `compute_hash` (SHA-256 placeholder, `opaque`) is the only uninterpreted constant; collision resistance is carried as an explicit theorem hypothesis (`hash_cr`), discharged at each call site, not a global axiom |
| [`OmegaP1Governance.lean`](./OmegaP1Governance.lean) | `P1_Governance` as a concrete predicate over the contract-and-agent presence pair; 2 theorems on contract and agent necessity | 0 | none |
| [`FailureProtocol.lean`](./FailureProtocol.lean) | `FailureAction` inductive with six cases (`retry`, `dead_letter`, `escalate_first`, `escalate_second`, `kill`, `circuit_breaker`); 1 theorem linking retry-limit overflow to escalation | 0 | none |

`OmegaProof.lean`, `OmegaV14.lean`, and `OmegaP1Governance.lean` are axiom-free at the user level — they rely only on Lean's standard built-ins (`Eq.refl` / `propext` and friends introduced implicitly by tactics) and use only `Prop`, `∧`, `¬`, `fun`, and `Iff`. `OmegaP3Semantic.lean` is in a deliberately different posture: it models a concrete hash chain and introduces one `opaque` declaration — `compute_hash` (a SHA-256 placeholder, to be replaced by VCVio's verified implementation — see *Next step* below). It declares **no user axioms**: collision resistance is carried as an explicit theorem hypothesis (`hash_cr`) discharged at each call site, so `tamper_detection` depends only on Lean built-ins (`#print axioms` → `[propext, Classical.choice, Quot.sound]`). The constructive core `tamper_implies_collision`, the encoding-injectivity theorem `canonicalBytes_injective_wf`, and the decoder roundtrip `decode_encode` likewise depend on no user axioms. `FailureProtocol.lean` carries no `sorry`: the monitoring obligation for excessive-retries-with-success is deliberately **not** encoded as a Lean theorem (it would require an axiom asserting the design choice), and is documented in [`failure-protocol.md`](./failure-protocol.md) instead.

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

## Verification status — historical receipt (superseded)

> **Superseded — retained for history only; do not run these.** This block
> recorded an earlier `v4.18.0`-pinned state and a since-removed axiom
> (`compute_hash_collision_resistant`), so its `#print axioms` receipts no
> longer match the source — in particular it showed
> `tamper_detection` depending on `compute_hash_collision_resistant`, which
> is no longer a declaration (collision resistance is now the explicit
> hypothesis `hash_cr`). The current machine-checked status — toolchain
> `v4.27.0`, **zero user-declared axioms** — is in *Verification status
> (2026-06-12)* at the top of this file, and is re-derived on every push by
> the workflow described in *Continuous Reproducibility*; run the commands there.

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
#print axioms retries_exceed_limit_implies_escalation
EOF
lake env lean /tmp/axioms.lean
```

## Continuous Reproducibility

`ATTESTATION_MANIFEST.md` is a claim about one run on one machine. [`.github/workflows/reproducibility.yml`](./.github/workflows/reproducibility.yml)
is the machine that re-checks that claim on a different one, from a clean checkout, on every push and pull
request. Treat it as part of the assurance argument, not as build hygiene.

**What it verifies.** Each of these fails the workflow:

1. The running Lean is the toolchain pinned in [`lean-toolchain`](./lean-toolchain) (`v4.27.0`).
2. The shipped library builds.
3. All seven bindings compile. The binding list is **discovered from the tree, not hardcoded**, and the count is
   checked against `EXPECTED_BINDINGS` (7), so neither an added binding that nobody attested nor a deleted one
   can pass unnoticed.
4. **Determinism.** Each binding is compiled twice on the runner and must be byte-identical.
5. **Independent re-check.** SafeVerify, built from pinned commit `b291b58` (never a tag), kernel-typechecks
   every declaration on a rebuilt expression tree. Its own digest is recorded in each run.
6. **Axiom policy**, two tiers, read out of the sources rather than hardcoded:
   - *Attested* theorems, meaning those named by a `#print axioms` line in a binding (currently 44), must
     depend on **zero** axioms. Because that set is read from the sources it could also shrink with them, so a
     coverage floor (`MIN_ATTESTED`, 44) fails the run if theorems are removed from the attested set. Raising
     it is routine; lowering it is a reviewable act.
   - *Generated* declarations, meaning the structure lemmas, `Repr` instances and recursors Lean synthesises,
     must stay inside the kernel allowlist `{propext, Quot.sound, Classical.choice}`. Several of them do use
     `propext`. They are not claims anyone made, and the strict tier is not applied to them.

Receipts, digests, the verifier digest and the log are uploaded as artifacts on every run, pass or fail.

**Running it locally.**

```bash
bash attested/verify-lean.sh    # exactly what CI runs
bash attested/reproduce.sh      # the above, plus the CryptoVerif / Z3 / TLA+ lanes
```

`reproduce.sh` additionally needs the sibling repositories and the CryptoVerif, Z3 and TLA+ toolchain, so it
runs on a configured machine and not from a clean checkout.

**What a green run guarantees.** At the pinned toolchain, from a clean checkout, on a machine that is not the
author's: the seven bindings compile, rebuild byte-identically, survive an independent kernel re-typecheck by a
separately-built verifier, and the attested theorems depend on no axioms at all, which is strictly stronger
than "no custom axioms".

**What it does not guarantee.** Stated plainly, because a green tick that is read wider than it holds is worse
than no tick:

- **It does not run the CryptoVerif, Z3 or TLA+ lanes.** Those read inputs from sibling repositories outside
  this one and cannot run from a clean checkout. The logs in `attested/correspondence/` are from the author's
  machine and are **not** re-derived by CI. Three of the four paradigms in the manifest are therefore attested
  by assertion here, not by this workflow.
- **It does not establish cross-platform bit-identity.** `.olean` files are platform-specific. The digests the
  Linux runner produces are not expected to equal the macOS digests in `ATTESTATION_MANIFEST.md`, and the
  workflow does not compare them. Determinism is checked within a run on one host, not across hosts.
- **It does not make the verifier trusted.** A green run inherits as its trusted base the Lean kernel, SafeVerify
  (built from a pinned commit, never cached, digest recorded each run), and the prebuilt Mathlib oleans that
  `lake exe cache get` fetches in order to build SafeVerify. That last one is a binary artifact from an upstream
  cache and it is trusted, not verified, here.
- **It does not defend against a pull request that edits its own gate.** `verify-lean.sh` and
  `check_receipts.py` live in the tree they check, so a PR can weaken the check and the weakened check is what
  runs against it. The workflow is an honest-error detector, not an adversary-resistant one. Read the diff to
  the checker, not just the tick.
- **It does not say the definitions model anything real.** Lean proves statements about definitions. Whether
  those definitions describe a running system is out of scope here: see [`docs/ASSURANCE_BOUNDARY.md`](./docs/ASSURANCE_BOUNDARY.md).

## Toolchain and Mathlib

- **Mathlib:** not required and not pulled — there is no `import Mathlib` in any shipped module, and the package declares **no external Lake dependencies** (`lakefile.lean`: the shipped roots are self-contained; VCVio was removed 2026-06-09).
- **Toolchain:** pinned to `leanprover/lean4:v4.27.0` (see [`lean-toolchain`](./lean-toolchain) and `lakefile.lean`).

## Next step

The next major step is to replace the `compute_hash` opaque declaration in `OmegaP3Semantic.lean` with the verified SHA-256 implementation from [VCVio](https://github.com/dtumad/VCV-io). VCVio's `LibSodium/SHA2.lean` slot is upstream-empty at v4.27.0; a future commit will wire it through (or via a local FFI module) once that slot is populated. After the substitution, `compute_hash` would no longer be an uninterpreted placeholder; collision resistance (carried as the explicit `hash_cr` hypothesis, **not** an axiom) would remain the irreducible cryptographic assumption.

## Legacy path on the public site

The canonical downloadable v1.2 artifact remains at  
`https://omegaprotocol.org/omega/formal-proof/omega_v12_lean4_proof.lean`  
(this repository's `v12-source/` copy matches that file for provenance).

## Source file hashes (SHA-256, at 6aa9008)

Per-file source hashes for the ten shipped roots and the four JCS encoder
modules, recorded here (canonical home for verification detail; moved from the
formal-proof page on the site).

| File | SHA-256 |
|------|---------|
| OmegaProof.lean | `2871ed6e76473b64df394be201ef4a2eecfb50029327d334a4d58014ca1c4e64` |
| OmegaV14.lean | `0f2b471eed18fea5e27c5515e223cf0f11fb82881befb5adf38d453c83a5423e` |
| OmegaP3Semantic.lean | `48c402f669b7ed9f2db39f5ae7cad26f0c07a58c7c650b6cbdf3538410deef50` |
| OmegaP1Governance.lean | `a7367304f44ae727f384dcdc119dc282b87d9aaf5743f59f2fed82fd689990bb` |
| FailureProtocol.lean | `cab7e95fa2cdb978b0d2523594a5fc4470eae6525c5772fb235f00167d30aab7` |
| OmegaHashChain.lean | `fcb3f76359da240c1d31efecfc68825acab042c0841e91cc193a239cf71e3b8f` |
| OmegaGovernance.lean | `8c9d5e7f8fd392febd72df5ef5e296a2d7c08b8eac3831e6aa8569397fcf2231` |
| OmegaJCSChain.lean | `4ba90bd45f4c6c4c879de8a5e7d0301d9ae77ff14677a1d1d9c7136562ad7c30` |
| OmegaP5Gate.lean | `46f5c3df0543cf5f7c628fc262214a7ceaa5edf26f21a10e57f86ee40d4d26a8` |
| OmegaProvenance.lean | `fbc62b16008782c8393e32d5af2fd225cd77ce07413bea78e537d1c5e97acfa9` |
| OmegaJCS/Types.lean | `d55877043733e6c02bb802e22375da8c2946b1ab5d2772712759272b12906d3a` |
| OmegaJCS/Encode.lean | `e7bb1484756dff6c1ad2f921aed00c4a5d18ff57b0741af17de17e4f5f48c10b` |
| OmegaJCS/Decode.lean | `388c4f93324d614e02d8b84f67908fcfa7af409c95e9f9a66e3d5358067d46cd` |
| OmegaJCS/Roundtrip.lean | `8c124bd755fff23b7d8545237613e53007e10ded32ab0e3d328d95ef1170e8a4` |

`lean4lean` v4.29 segfaults on `OmegaProof`; SafeVerify v4.27 is used for attestation.
