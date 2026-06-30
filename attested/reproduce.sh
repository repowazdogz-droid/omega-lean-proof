#!/usr/bin/env bash
# Reproduce the OMEGA polyglot binding attestation (HELD — internal).
# Run from ~/Omega/lean-proof:  bash attested/reproduce.sh
set -uo pipefail
cd "$(dirname "$0")/.."   # -> ~/Omega/lean-proof
ROOT="$PWD"
REC="$ROOT/attested/correspondence"
OLE="$ROOT/attested/oleans"
RCP="$ROOT/attested/receipts"
mkdir -p "$REC" "$OLE" "$RCP"

SV="$ROOT/.cache/SafeVerify/.lake/build/bin/safe_verify"
JAVA=/opt/homebrew/opt/openjdk@17/bin/java
JAR=/Users/warre/tla-omega/tla2tools.jar
CV=/Users/warre/.opam/proverif/bin/cryptoverif
BINDINGS="OmegaP6ABinding OmegaP4MBinding OmegaP6AtomicBinding OmegaP12Binding OmegaP2DAGBinding OmegaP4TBinding OmegaP6LBinding"

echo "== [0] clean shipped build (oleans for OmegaV14 etc.) =="
lake build >/dev/null 2>&1 && echo "  lake build OK" || { echo "  lake build FAILED"; exit 1; }

echo "== [A] Lean bindings: compile -> SafeVerify self-replay =="
export LEAN_PATH="$ROOT/.lake/build/lib/lean"
for b in $BINDINGS; do
  lake env lean -o "$OLE/$b.olean" "$b.lean" >/dev/null 2>&1 || { echo "  $b compile FAILED"; exit 1; }
  if "$SV" "$OLE/$b.olean" "$OLE/$b.olean" --save "$RCP/$b.json" >/dev/null 2>&1; then
    echo "  $b: SafeVerify PASS"
  else
    echo "  $b: SafeVerify FAIL"; exit 1
  fi
done

echo "== [B1] CryptoVerif =="
( cd "$ROOT/../crypto-conjuncts-cv"
  for f in PChainIntegrity_cr P5E_attestation P5E_attestation_weak P11link_unforgeable P11link_unforgeable_weak; do
    "$CV" "$f.cv" > "$REC/cv_$f.log" 2>&1
    echo "  $f: $(grep -E 'All queries proved|Could not prove' "$REC/cv_$f.log" | head -1)"
  done )

echo "== [B2] Z3 / P10 =="
python3 "$ROOT/../p10-competence-z3/p10_competence.py" > "$REC/z3_p10_competence.log" 2>&1
echo "  P10: $(grep 'ALL THREE' "$REC/z3_p10_competence.log")"

echo "== [B3] TLA+ / TLC =="
tlc() { ( cd "$ROOT/../$1"; "$JAVA" -cp "$JAR" tlc2.TLC -deadlock -config "$3" "$2" > "$REC/tla_$4.log" 2>&1 ); }
tlc p5-confirmation-tla    P5Confirmation.tla    P5_weak.cfg          p5_weak
tlc p5-confirmation-tla    P5Confirmation.tla    P5_repaired.cfg      p5_repaired
tlc p5-confirmation-tla    P5Confirmation.tla    P5_nonvacuity.cfg    p5_nonvacuity
tlc p11-update-integrity-tla P11UpdateIntegrity.tla P11_weak.cfg      p11_weak
tlc p11-update-integrity-tla P11UpdateIntegrity.tla P11_repaired.cfg  p11_repaired
tlc p11-update-integrity-tla P11UpdateIntegrity.tla P11_nonvacuity.cfg p11_nonvacuity
tlc p1-freshness-tla       P1Freshness.tla       P1Freshness_weak.cfg       p1_weak
tlc p1-freshness-tla       P1Freshness.tla       P1Freshness_repaired.cfg   p1_repaired
tlc p1-freshness-tla       P1Freshness.tla       P1Freshness_nonvacuity.cfg p1_nonvacuity
for t in p5_weak p5_repaired p5_nonvacuity p11_weak p11_repaired p11_nonvacuity p1_weak p1_repaired p1_nonvacuity; do
  echo "  $t: $(grep -E 'is violated|No error has been found' "$REC/tla_$t.log" | head -1 | cut -c1-60)"
done
echo "== done (HELD — do not publish) =="
