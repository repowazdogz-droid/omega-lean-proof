# Instrumented Proof Sprint — lean-proof

Run 2026-06-10 → 2026-06-11. Both engineering and evidence: every attempt logged to `proof-sprint-log.jsonl`. Read-only on shipped roots; all work confined to scratch + this report.

## Headline

**The "30 sorrys" were not 30 open proof obligations.** A `grep '\bsorry\b'` counts the *word* "sorry", and the reality after triage is:

- **11** are the word "sorry" inside **comments/docstrings** ("no `sorry`", "Zero sorry", "use sorry initially"). Not proof gaps.
- **18** are **superseded development probes** in `scratch/*.lean` — abandoned files that no longer compile (1–33 errors each), whose target lemmas are **already proven, zero-sorry, in the shipped `OmegaJCS` library**.
- **1** is a genuine open obligation in the `OmegaV15` draft (`[O2] p6_no_coalition_escape`) — and it is **false as written** (suspected-false → BLOCKED, machine-checked below).

**The shipped formal artifact was already complete and sorry-free.** A `lake build` (baseline and final) is green with **zero `uses 'sorry'` warnings** across all shipped roots, and the repo's own `CLAUDE.md` states the same. There was nothing legitimate to close.

> Correction to prior `aria-ta2-fitgap.md`: that report's "126 files / 30 sorry / scaffolding incomplete" over-counted. The shipped proof (OmegaJCS roundtrip+injectivity, hash-chain, governance bundles) is **0-sorry**; the 19 real sorrys are all in non-built draft/scratch, 18 of them superseded by the shipped proofs.

## Scoreboard

| Metric | Value |
|---|---|
| Baseline `lake build` | **green**, ~3.35 s (final: 0.47 s incremental), 15 jobs, **0 sorry warnings** |
| grep `sorry` total | 30 (→ 11 comments, 19 real) |
| Real sorrys in **shipped build**, before → after | **0 → 0** |
| Real sorrys total (incl. draft+scratch), before → after | 19 → 19 |
| **Sorrys closed** | **0** (0 were legitimately closable) |
| New theorems proven | **1** — `o2_premise_too_weak` (axiom-free) |
| BLOCKED / SUSPECTED-FALSE | 1 (`[O2] p6_no_coalition_escape`) |
| SUPERSEDED (already proven in shipped lib) | 19 |
| New axioms introduced | **0** (hard rule honoured) |
| Total attempt wall-clock | ~85 min |

## Per-theorem log

| Theorem / target | File | Result | Diff | Min | Axiom check |
|---|---|---|---|---|---|
| `p6_no_coalition_escape` [O2] | OmegaV15.lean:703 | **BLOCKED** | SUSPECTED-FALSE | 18 | n/a |
| `arr_mem_wf` (WF propagation) | scratch/WfBoolProbe.lean:19 | **SUPERSEDED** (verified 1-line via shipped `arr_wf_all`, then reverted) | EASY | 12 | PASS `[propext, Classical.choice, Quot.sound]` |
| `o2_premise_too_weak` (O2 counterexample) | scratch/O2Counterexample.lean | **CLOSED** (new) | EASY | 20 | **PASS — no axioms at all** |
| 18 scratch probe sorrys | scratch/*.lean | **SUPERSEDED** (abandoned non-compiling; lemmas shipped) | n/a | 35 | n/a |

No `lake build` rot occurred: tree green at baseline and final; only untracked scratch + docs added.

## Evidence paragraph (honest, funding-grade)

> In an instrumented sprint against this repository's apparent 30-`sorry` backlog, **AI assistance closed zero proof obligations — because there were none to close.** Triage showed the shipped Lean 4 artifact (JCS canonicalization round-trip and injectivity, the append-only hash-chain tamper-detection theorem, and the v1.3/v1.4.1 governance bundles) was **already machine-checked sorry-free**, confirmed by a green `lake build` with no `sorry` warnings and a single declared user axiom (`compute_hash_collision_resistant`). Of the 30 grep hits, 11 were the word "sorry" in comments and 18 were abandoned development scratch whose target lemmas — e.g. the `\uXXXX` control-character round-trip `hex4Lower_parseHex4` — are present and **proven, byte-for-byte, in the shipped library** (`OmegaJCS/Roundtrip.lean:91`). The one genuine open obligation, `p6_no_coalition_escape` in the non-shipped `OmegaV15` draft, was found to be **false as written**, and AI assistance was used not to prove it but to **mechanically refute its provability**: a four-line, **axiom-free** Lean theorem (`o2_premise_too_weak`) exhibits a boundary satisfying the hypothesis while falsifying the conclusion. The honest lesson for an AI-enabled-formal-methods bid is therefore about **measurement and falsification, not search**: the headline sorry-count was an artifact, the real assurance surface was already closed, and the highest-value AI contribution was distinguishing a complete proof from an incomplete one and proving a stated obligation unsound rather than papering over it.

## BLOCKED / SUSPECTED-FALSE — full analysis

### `[O2] OmegaV15.p6_no_coalition_escape` — SUSPECTED-FALSE

Statement (unedited):
```lean
theorem p6_no_coalition_escape
    (h   : (detectCoupling log graph).length > 0)
    (h_b : P6_AgencyBoundary_Holds b) :
    (b.mode_P6D_DelegatedOrCoalition = true ∧ b.delegation_explicitly_declared = true) ∨
    (b.mode_P6C_CouplingClosure       = true ∧ b.coupling_closure_satisfied       = true)
```
with
```lean
def P6_AgencyBoundary_Holds (b) : Prop :=
  b.mode_P6A_AtomicSingleActor = true ∨
  (b.mode_P6D_DelegatedOrCoalition = true ∧ b.delegation_explicitly_declared = true) ∨
  (b.mode_P6C_CouplingClosure = true ∧ b.coupling_closure_satisfied = true)
```

**Why it cannot be proved as written.** The conclusion is the *last two* disjuncts of `P6_AgencyBoundary_Holds`, but the predicate also admits the **first** disjunct, `mode_P6A_AtomicSingleActor = true`. The only other hypothesis, `h`, constrains `detectCoupling log graph` — and `log`, `graph`, `b` are **independent `variable`s** with no stated relation. So the hypotheses do not exclude an atomic-single-actor boundary.

**Machine-checked counterexample** (`scratch/O2Counterexample.lean`, **depends on no axioms**):
```lean
theorem o2_premise_too_weak :
    ∃ b : P6AgencyBoundary, P6_AgencyBoundary_Holds b ∧
      ¬ ((b.mode_P6D_DelegatedOrCoalition = true ∧ b.delegation_explicitly_declared = true) ∨
         (b.mode_P6C_CouplingClosure = true ∧ b.coupling_closure_satisfied = true)) := by
  refine ⟨⟨true, false, false, false, false⟩, ?_, ?_⟩
  · exact Or.inl rfl
  · decide
```
`b = ⟨true,false,false,false,false⟩` (atomic single actor) satisfies the premise yet falsifies the conclusion. The theorem is therefore unprovable until a **schema invariant ties `detectCoupling log graph > 0` to `¬ b.mode_P6A`** — i.e. the model must connect the coupling actually detected in `(log, graph)` to the boundary `b` that is accepting the action. The docstring already concedes the proof "requires concrete `MemoryAccessLog` and `DeploymentGraph` schemas"; this confirms that gap is load-bearing, not cosmetic. **Per sprint rules the original statement was not edited.** Recommended fix (for a future, scoped task): add a hypothesis `h_link : detectCoupling log graph ≠ [] → b.mode_P6A_AtomicSingleActor = false`, or fold the coupling evidence into `P6_AgencyBoundary_Holds`.

### The 18 scratch sorrys — SUPERSEDED (a finding, not a failure)

All 11 `scratch/*.lean` probe files fail to compile (1–33 errors each); in most, elaboration errors upstream so the `sorry` is never reached. They are frozen mid-exploration. Crucially, the lemmas they were reaching toward are **already proven, zero-sorry, in the shipped library** — verified directly:
- `hex4Lower_parseHex4` (control-char `\uXXXX` round-trip) — scratch copy is byte-identical to the **proven** `OmegaJCS/Roundtrip.lean:91` (with helpers `hexValue∘hexDigit` roundtrip at :72 and `hex4_recomb_small` at :76).
- WF-propagation (`x ∈ arr xs → x.WF`) — shipped as `OmegaJCS/Types.arr_wf_all`.
- string/number round-trip — shipped as `parseString_jcsEscapeString` (:196) and the number-parse section.

Closing these would re-derive shipped results in broken files: zero assurance gain. They are best **deleted** as superseded scratch in a future cleanup, not "proved."
