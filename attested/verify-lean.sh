#!/usr/bin/env bash
# In-repo Lean attestation lane. Single source of truth: reproduce.sh calls this
# for step [A], and CI (.github/workflows/reproducibility.yml) calls it directly.
#
# Verifies, and fails on any of:
#   1. the running Lean is not the toolchain pinned in ./lean-toolchain
#   2. the shipped library does not build
#   3. a binding does not compile
#   4. a binding is not byte-identical when rebuilt (non-deterministic build)
#   5. SafeVerify self-replay does not pass (kernel re-typecheck of every declaration)
#   6. any theorem depends on any axiom (zero-axiom policy; see check_receipts.py)
#
# Deliberately does NOT cover the CryptoVerif / Z3 / TLA+ lanes: those read inputs
# from sibling repositories outside this one and cannot run from a clean checkout.
set -euo pipefail

cd "$(dirname "$0")/.."
ROOT="$PWD"

# Discovered from the tree, never hardcoded: a hardcoded list means a binding added
# to the repo is silently never attested, and CI stays green while it sits there.
# EXPECTED_BINDINGS then catches the other direction, a binding being deleted.
BINDINGS=()
for f in "$ROOT"/OmegaP*Binding.lean; do
  [ -e "$f" ] || break
  BINDINGS+=("$(basename "$f" .lean)")
done
EXPECTED_BINDINGS="${EXPECTED_BINDINGS:-7}"
if [ "${#BINDINGS[@]}" -ne "$EXPECTED_BINDINGS" ]; then
  echo "FAIL: found ${#BINDINGS[@]} bindings (${BINDINGS[*]:-none}), expected $EXPECTED_BINDINGS."
  echo "      If this is intended, update EXPECTED_BINDINGS and the attestation manifest together."
  exit 1
fi

SV="${SAFE_VERIFY:-$ROOT/.cache/SafeVerify/.lake/build/bin/safe_verify}"
OLE="${OLEAN_DIR:-$ROOT/attested/oleans}"
RCP="${RECEIPT_DIR:-$ROOT/attested/receipts}"
SUMS="${SUMS_FILE:-$OLE/SHA256SUMS}"

REBUILD="$(mktemp -d)"
trap 'rm -rf "$REBUILD"' EXIT
mkdir -p "$OLE" "$RCP"

[ -x "$SV" ] || { echo "FAIL: safe_verify not found or not executable at $SV"; exit 1; }

echo "== [1] toolchain pin =="
want="$(tr -d '[:space:]' < "$ROOT/lean-toolchain")"          # leanprover/lean4:v4.27.0
want_ver="${want#leanprover/lean4:v}"                          # 4.27.0
got_ver="$(lake env lean --version | sed -E 's/.*version ([^,]+),.*/\1/')"
if [ "$want_ver" != "$got_ver" ]; then
  echo "FAIL: pinned Lean is $want_ver but $got_ver is running"; exit 1
fi
echo "  Lean $got_ver (pinned)"

echo "== [2] shipped library builds =="
lake build >/dev/null
export LEAN_PATH="$ROOT/.lake/build/lib/lean"

echo "== [3] bindings: compile, rebuild-determinism, SafeVerify self-replay =="
for b in "${BINDINGS[@]}"; do
  lake env lean -o "$OLE/$b.olean"     "$b.lean" >/dev/null
  lake env lean -o "$REBUILD/$b.olean" "$b.lean" >/dev/null

  h1="$(shasum -a 256 "$OLE/$b.olean"     | cut -d' ' -f1)"
  h2="$(shasum -a 256 "$REBUILD/$b.olean" | cut -d' ' -f1)"
  if [ "$h1" != "$h2" ]; then
    echo "FAIL: $b is not deterministic ($h1 != $h2 on the same host)"; exit 1
  fi

  # Self-replay: every declaration is kernel-typechecked on a rebuilt expression
  # tree, and its axiom set is checked against SafeVerify's allowlist.
  if ! "$SV" "$OLE/$b.olean" "$OLE/$b.olean" --save "$RCP/$b.json" >/dev/null 2>&1; then
    echo "FAIL: $b did not pass SafeVerify self-replay"; exit 1
  fi
  echo "  $b: deterministic ($h1), SafeVerify PASS"
done

echo "== [4] zero-axiom policy over the receipts =="
python3 "$ROOT/attested/check_receipts.py" "$RCP" "${BINDINGS[@]}"

echo "== [5] digests =="
( cd "$OLE" && shasum -a 256 "${BINDINGS[@]/%/.olean}" > "$SUMS" )
cat "$SUMS"

echo "== Lean attestation lane: PASS =="
