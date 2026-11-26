#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean --version
lake --version
lake exe cache get Mathlib.Tactic Mathlib.Algebra.Polynomial.Coeff Mathlib.Algebra.Polynomial.Inductions Mathlib.Algebra.Polynomial.Degree.Lemmas Mathlib.RingTheory.PowerSeries.Basic Mathlib.Analysis.Calculus.Deriv.MeanValue Mathlib.Analysis.Calculus.Deriv.Pow Mathlib.Analysis.Calculus.Deriv.Shift Mathlib.Analysis.Calculus.DSlope
git -C .lake/packages/mathlib rev-parse HEAD
lake build
audit_output=$(mktemp)
trap 'rm -f "$audit_output"' EXIT
lake env lean Audit.lean | tee "$audit_output"
python3 - "$audit_output" <<'PY'
import pathlib
import re
import sys
expected_names = re.findall(r"^#print axioms (\S+)$", pathlib.Path("Audit.lean").read_text(), re.M)
records = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", pathlib.Path(sys.argv[1]).read_text()))
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name in expected_names:
    if name not in records or set(records[name].split(", ")) - allowed:
        raise SystemExit(f"Unexpected or missing axiom report for {name}")
for path in sorted(pathlib.Path("SZ").glob("*.lean")) + [pathlib.Path("SZ.lean"), pathlib.Path("Audit.lean")]:
    if re.search(r"\b(sorry|admit|sorryAx|axiom|native_decide)\b", path.read_text()):
        raise SystemExit(f"Unexpected proof placeholder or trust declaration in {path}")
print(f"Checked {len(expected_names)} axiom reports and the local Lean sources.")
PY
