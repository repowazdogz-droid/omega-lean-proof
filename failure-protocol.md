# Failure protocol — Lean-proof local spec

This file holds the operational rules that the Lean module `FailureProtocol.lean`
formalises (or deliberately does not formalise). The canonical broader spec lives
at `../unified-forge/failure-protocol.md`; this file scopes the rules to the
predicates that appear in the Lean source.

## Retry limit

Two attempts per discrete failure (`retries_exceed_limit r ≡ r > 2`). Further
retries require explicit human authorization or an updated goal contract.

## Escalation rule (formalised in Lean)

When retries exceed the limit **and** verification did not pass, escalation is
required. This is the theorem `retries_exceed_limit_implies_escalation` in
`FailureProtocol.lean`: a direct conjunction-introduction proof.

## Monitoring rule (operational; not a Lean theorem)

When retries exceed the limit **but** verification did pass (the
`retries_with_success` case), the operational requirement is that the run be
flagged for monitoring rather than escalated as a failure. The reasoning:
excessive retries even after a successful verification indicate systemic
instability that should be surfaced for human review without halting the run.

This rule is **part of the operational spec, not a logical consequence** of the
retry arithmetic. It is intentionally not stated as a Lean theorem, because
any such "theorem" would either (a) require an axiom asserting the spec rule, or
(b) collapse to a definitional rename whose proof is the identity function and
which carries no semantic content. The honest place for the rule is here, in
prose, where it can be read, audited, and changed without dressing it up as a
mathematical consequence.

## Dead letter and kill conditions

See `../unified-forge/failure-protocol.md` for the broader operational matrix
(dead-letter handling, circuit-breaker, kill conditions, credential exposure
handling). The Lean module formalises only the retry-limit and escalation
predicates from that document.
