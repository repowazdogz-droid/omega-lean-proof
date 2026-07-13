#!/usr/bin/env python3
"""Enforce the axiom policy over SafeVerify receipts.

Two tiers, because the two populations of declaration in a binding's .olean carry
different claims:

  ATTESTED   Every theorem named by a `#print axioms` line in the binding source.
             These are the proof obligations the attestation is about. Policy:
             ZERO axioms. Not "no custom axioms" -- none at all.

  GENERATED  Everything else in the .olean: structure lemmas (.mk.injEq), Repr
             instances, recursors and other declarations Lean synthesises. Several
             of these legitimately use propext. They are not claims anyone made.
             Policy: must stay inside the kernel allowlist below.

The attested set is read out of the .lean sources rather than hardcoded here, so
adding a theorem to a binding without attesting it cannot silently widen the claim.

The attested set is derived from the sources, which means it can also SHRINK with the
sources: delete the `#print axioms` lines and the check would happily verify whatever
is left and still report success. MIN_ATTESTED is the floor that stops that being
silent. Raise it when theorems are added; lowering it is a deliberate, reviewable act.

Usage: check_receipts.py <receipt-dir> <binding> [<binding> ...]
Env:   MIN_ATTESTED (default 44)
"""

import json
import os
import re
import sys
from pathlib import Path

ALLOWLIST = {"propext", "Quot.sound", "Classical.choice"}
MIN_ATTESTED = int(os.environ.get("MIN_ATTESTED", "44"))
PRINT_AXIOMS = re.compile(r"^\s*#print\s+axioms\s+([A-Za-z_][\w.']*)\s*$", re.M)


def main() -> int:
    receipt_dir, bindings = Path(sys.argv[1]), sys.argv[2:]
    root = Path(__file__).resolve().parent.parent
    if not bindings:
        print("FAIL: no bindings named", file=sys.stderr)
        return 1

    violations = []
    attested_seen = 0

    for name in bindings:
        source, receipt = root / f"{name}.lean", receipt_dir / f"{name}.json"
        if not receipt.exists():
            violations.append(f"{name}: no receipt at {receipt}")
            continue
        if not source.exists():
            violations.append(f"{name}: no source at {source}")
            continue

        # The claim, taken from the source: fully-qualified names of attested theorems.
        attested = {f"{name}.{m}" for m in PRINT_AXIOMS.findall(source.read_text())}
        if not attested:
            violations.append(f"{name}: source attests no theorems (#print axioms absent)")
            continue

        found = set()
        for decl, info in json.loads(receipt.read_text()):
            if info.get("failureMode") is not None:
                violations.append(f"{decl}: failureMode={info['failureMode']!r}")

            axioms = set()
            for side in ("targetInfo", "solutionInfo"):
                axioms |= set((info.get(side) or {}).get("axioms") or [])

            if decl in attested:
                found.add(decl)
                if axioms:
                    violations.append(
                        f"ATTESTED {decl}: must depend on zero axioms, depends on {', '.join(sorted(axioms))}"
                    )
            elif not axioms <= ALLOWLIST:
                violations.append(
                    f"GENERATED {decl}: {', '.join(sorted(axioms - ALLOWLIST))} outside kernel allowlist"
                )

        missing = attested - found
        if missing:
            violations.append(f"{name}: attested but absent from receipt: {', '.join(sorted(missing))}")
        attested_seen += len(found)

    if attested_seen < MIN_ATTESTED:
        violations.append(
            f"coverage floor: {attested_seen} attested theorems checked, "
            f"MIN_ATTESTED={MIN_ATTESTED}. Theorems were removed from the attested set."
        )

    if violations:
        print(f"FAIL: axiom policy violated ({len(violations)}):")
        for v in violations:
            print(f"  {v}")
        return 1

    print(f"  {attested_seen} attested theorems: zero axioms (floor {MIN_ATTESTED})")
    print(f"  generated declarations: within allowlist {{{', '.join(sorted(ALLOWLIST))}}}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
