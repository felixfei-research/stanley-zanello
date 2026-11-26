#!/usr/bin/env python3
"""Reproducible finite checks for the Stanley--Zanello difference.

Requires Python 3.9+ and its standard library. No floating-point arithmetic is
used for mathematical calculations. Timings are the only floating-point data.
This program is a finite diagnostic, not a proof of an eventual assertion.

The tested polynomial is
    F(q) = [k+ell choose k]_q - q**s [k-2+t choose k-2]_q,
where (k-2)*t + 2*s = k*ell, with nonnegative integer t and s.

The primary scan stops at the first negative first difference in the left
half, as did the original program. A separate direct-coefficient audit retains
EVERY negative left-half first difference for EVERY failing tuple. Counts of
primary inspections exclude these additional independent checks.
"""

import argparse
import csv
import hashlib
import io
import json
import platform
import shlex
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import comb, factorial
from pathlib import Path


VERSION = "2.0"


def require(condition, message):
    """Keep verification active even under python -O."""
    if not condition:
        raise RuntimeError(message)


def canonical_bytes(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def digest(value):
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


@lru_cache(maxsize=None)
def gaussian_product(r, w):
    """Exact polynomial multiplication and formal-series division.

    At stage j the complete polynomial has degree j*w. Multiplication by
    (1-q**(w+j)), followed by division by (1-q**j), is therefore truncated at
    that known degree. The latter operation uses integer prefix additions.
    """
    require(r >= 0 and w >= 0, "Negative Gaussian parameter")
    if not r or not w:
        return (1,)
    if w < r:
        return gaussian_product(w, r)
    a = [1]
    for j in range(1, r + 1):
        degree = w * j
        out = [0] * (degree + 1)
        for n, value in enumerate(a):
            out[n] += value
            if n + w + j <= degree:
                out[n + w + j] -= value
        for n in range(j, degree + 1):
            out[n] += out[n - j]
        a = out
    require(len(a) == r * w + 1 and a[0] == a[-1] == 1,
            "Gaussian degree or endpoint invariant failed")
    require(min(a) >= 0, "Negative Gaussian coefficient")
    require(a == a[::-1], "Gaussian symmetry invariant failed")
    require(sum(a) == comb(r + w, r), "Gaussian value at q=1 failed")
    return tuple(a)


def gaussian_pascal_selected(pairs):
    """Independent iterative q-Pascal method; no product coefficients used.

    G(r,w) = G(r,w-1) + q**w G(r-1,w). Only the current width is retained,
    plus coefficient vectors explicitly requested by the caller. This avoids
    recursion-depth dependence and a full two-dimensional coefficient cache.
    """
    pairs = set(pairs)
    max_r = max(r for r, _ in pairs)
    max_w = max(w for _, w in pairs)
    needed = [max((w for r, w in pairs if r >= j), default=0)
              for j in range(max_r + 1)]
    rows = [(1,) for _ in range(max_r + 1)]
    answer = {p: (1,) for p in pairs if 0 in p}
    states = 0
    for w in range(1, max_w + 1):
        for r in range(1, max_r + 1):
            if w > needed[r]:
                continue
            left, lower = rows[r], rows[r - 1]
            out = [0] * (r * w + 1)
            out[:len(left)] = left
            for n, value in enumerate(lower):
                out[n + w] += value
            rows[r] = tuple(out)
            states += 1
            if (r, w) in pairs:
                answer[r, w] = rows[r]
    require(set(answer) == pairs, "q-Pascal requests were not all computed")
    return answer, states


@lru_cache(maxsize=None)
def differences(r, w):
    a = gaussian_product(r, w)
    return tuple(a[n] - (a[n - 1] if n else 0) for n in range(len(a)))


def restricted_partitions(r, degree):
    """Coin-change coefficients of product(1-q**j)^(-1), j=2,...,r."""
    a = [0] * (degree + 1)
    a[0] = 1
    for part in range(2, r + 1):
        for n in range(part, degree + 1):
            a[n] += a[n - part]
    return a


def admissible_by_t(k, ell):
    return [(t, (k * ell - (k - 2) * t) // 2)
            for t in range(k * ell // (k - 2) + 1)
            if (k * ell - (k - 2) * t) % 2 == 0]


def admissible_by_s(k, ell):
    return sorted(((k * ell - 2 * s) // (k - 2), s)
                  for s in range(k * ell // 2 + 1)
                  if (k * ell - 2 * s) % (k - 2) == 0)


def primary_check(k, ell, t, s):
    da, db = differences(k, ell), differences(k - 2, t)
    for n in range(k * ell // 2 + 1):
        u = n - s
        value = da[n] - (db[u] if u >= 0 else 0)
        if value < 0:
            return {"n": n, "first_difference": value}, n + 1
    return None, k * ell // 2 + 1


def direct_case(k, ell, t, s, getter):
    """Build the full padded F from coefficients, then difference it directly."""
    a, b = getter(k, ell), getter(k - 2, t)
    c = list(a)
    for j, value in enumerate(b):
        c[j + s] -= value
    require(c == c[::-1], "Padded difference is not symmetric")
    require(c[0] == (0 if s == 0 else 1), "Wrong constant coefficient")
    negatives = []
    for n in range(len(c) // 2 + (len(c) % 2)):
        previous = c[n - 1] if n else 0
        if c[n] < previous:
            negatives.append({"n": n, "first_difference": c[n] - previous,
                              "coefficient_before": previous, "coefficient_at_n": c[n]})
    return {
        "negative_first_differences": negatives,
        "coefficient_minimum": min(c),
        "negative_coefficient_count": sum(x < 0 for x in c),
        "coefficient_sha256": digest(c),
        "first_three_coefficients": c[:3],
    }


def spline_main(k, ell, n):
    """Exact rational half-shifted leading term, not an error bound."""
    L = Fraction(2 * ell + k + 1, 2)
    delta = Fraction(k * ell + 1, 2) - n
    d = k - 2
    numerator = sum((-1) ** j * comb(k, j)
                    * max(Fraction(0), (Fraction(k, 2) - j) * L - delta) ** d
                    for j in range(k + 1))
    return numerator / (factorial(k) * factorial(d))


def half_shift_checks(max_k):
    """Target the shift and first-order cancellation used in the manuscript.

    These checks use exact rational arithmetic for leading coefficients and
    integer polynomial coefficients for the affine subset identity. They are
    finite algebra checks, not a symbolic proof for arbitrary k.
    """
    records = []
    for k in range(5, max_k + 1):
        d, S = k - 2, sum(range(2, k + 1))
        A = sum((Fraction(j - 1, 2) for j in range(2, k + 1)), Fraction(0))
        require(A == Fraction(k * (k - 1), 4), "Wrong first Laurent correction")
        require(Fraction(d + 1, 2) + A == Fraction(S, 2),
                "Wrong shift in the restricted-partition expansion")
        subset_count = 0
        sums = []
        for j in range(k + 1):
            epsilon_twice_sum = 0
            count = 0
            for subset in combinations(range(1, k + 1), j):
                subset_sum = sum(subset)
                epsilon_twice = 2 * subset_sum - j * (k + 1)
                epsilon_twice_sum += epsilon_twice
                # Compare coefficients of ell, n, and 1 in four times (3.6).
                left = (-4 * j, 4, 2 * S - 4 * subset_sum)
                right = (2 * (k - 2 * j) - 2 * k, 4,
                         (k + 1) * (k - 2 * j) - 2 - 2 * epsilon_twice)
                require(left == right, "Half-unit affine shift identity failed")
                count += 1
            require(count == comb(k, j), "Subset enumeration count failed")
            require(epsilon_twice_sum == 0, "First-order subset cancellation failed")
            subset_count += count
            sums.append(epsilon_twice_sum)
        records.append({"k": k, "subsets_checked": subset_count,
                        "twice_epsilon_sums_by_cardinality": sums,
                        "S_over_two": str(Fraction(S, 2))})
    return records


def compare_reference(result, failures, reference_path):
    """Compare every numerical statement retained by the original report."""
    if (result["range"]["max_k"], result["range"]["max_width"]) != (16, 160):
        return {"performed": False, "reason": "The reference scan is k=5..16, ell=1..160."}
    if not reference_path.is_file():
        return {"performed": False, "reason": "Reference results file is absent."}
    old = json.loads(reference_path.read_text(encoding="utf-8"))
    mapping = {
        "independent_gaussian_cross_checks": "legacy_grid_gaussian_cross_checks",
        "admissible_cases_excluding_shift_one": "admissible_cases_excluding_shift_one",
        "first_differences_inspected_including_exceptions": "first_differences_inspected_including_exceptions",
        "exact_edge_identity_checks": "exact_edge_identity_checks",
        "shift_one_nonunimodality_checks": "shift_one_nonunimodality_checks_width_at_least_two",
    }
    for key, new_key in mapping.items():
        require(old[key] == result[new_key], "Reference count mismatch: " + key)
    for previous, current in zip(old["per_k"], result["per_k"]):
        for key in ("k", "tested_widths", "admissible_cases_excluding_shift_one",
                    "finite_failure_count", "largest_failing_width_observed",
                    "m_corresponding_to_last_failure"):
            require(previous[key] == current[key], "Reference per-k mismatch: " + key)
        last = current["largest_failing_width_observed"]
        observed = [{key: f[key] for key in ("width", "t", "shift", "n", "first_difference")}
                    for f in failures if f["k"] == current["k"] and f["width"] == last]
        require(observed == previous["failures_at_largest_width"],
                "Reference last-width failure witnesses differ")
    require(len(old["per_k"]) == len(result["per_k"]), "Reference range length mismatch")
    require(old["spline_diagnostics"] == result["spline_diagnostics"],
            "Reference rational spline diagnostics differ")
    return {"performed": True, "all_retained_numerical_claims_match": True,
            "reference_file": reference_path.name,
            "reference_sha256": hashlib.sha256(reference_path.read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-k", type=int, default=16)
    parser.add_argument("--max-width", type=int, default=160)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--reference-results", type=Path,
                        default=Path(__file__).resolve().with_name("reference_original_results.json"))
    args = parser.parse_args()
    require(args.max_k >= 5 and args.max_width >= 1, "Empty or invalid scan range")
    start_utc = datetime.now(timezone.utc).isoformat()
    start_wall, start_cpu = time.perf_counter(), time.process_time()

    summaries, failures, exceptions = [], [], []
    selected_cases = set()
    base_pairs = {(r, w) for r in range(11) for w in range(16)}
    selected_pairs = set(base_pairs)
    parameter_hash = hashlib.sha256()
    primary_checks = edge_checks = all_cases = nonexception_cases = 0
    expected_primary_checks = expected_edge_checks = 0
    width_at_least_two_exceptions = 0
    parameter_rows = 0

    for k in range(5, args.max_k + 1):
        per_cases = per_failures = 0
        last_failure = 0
        for ell in range(1, args.max_width + 1):
            parameters = admissible_by_t(k, ell)
            require(parameters == admissible_by_s(k, ell), "Independent parameter enumerations differ")
            N, h = k * ell, k - 2
            floor_t = N // h
            closed_count = floor_t + 1 if h % 2 == 0 else (floor_t - N % 2) // 2 + 1
            require(len(parameters) == closed_count, "Closed-form parameter count differs")
            parameter_rows += 1
            per_width_nonexception = sum(s != 1 for _, s in parameters)
            expected_edge_checks += per_width_nonexception * (ell + 1)
            hlarge = restricted_partitions(k, ell)
            hsmall = restricted_partitions(h, ell)
            da = differences(k, ell)
            require(tuple(hlarge) == da[:ell + 1], "Large Gaussian edge identity failed")
            boundary_width = ell in {1, 2, max(1, args.max_width - 1), args.max_width}
            if boundary_width:
                chosen = parameters[:2] + parameters[-2:]
                chosen += [(t, s) for t, s in parameters if s in (0, 1, 2, 3)]
                selected_cases.update((k, ell, t, s) for t, s in chosen)
            for t, s in parameters:
                require(h * t + 2 * s == N, "Center alignment failed")
                require((N // 2 - s) <= h * t // 2, "Unsafe smaller-difference index")
                parameter_hash.update(f"{k},{ell},{t},{s}\n".encode())
                all_cases += 1
                witness, inspected = primary_check(k, ell, t, s)
                primary_checks += inspected
                expected_primary_checks += N // 2 + 1
                if witness is not None:
                    expected_primary_checks -= N // 2 - witness["n"]
                if s == 1:
                    direct = direct_case(k, ell, t, s, gaussian_product)
                    require(witness == {"n": 1, "first_difference": -1},
                            "Shift-one exception has wrong witness")
                    if ell >= 2:
                        require(direct["first_three_coefficients"] == [1, 0, 1],
                                "Shift-one initial coefficients differ")
                        width_at_least_two_exceptions += 1
                    else:
                        require(direct["first_three_coefficients"] == [1, 0, 0],
                                "Width-one exception has wrong initial coefficients")
                    exceptions.append({"k": k, "width": ell, "t": t, "shift": s,
                                       **witness, "first_three_coefficients": direct["first_three_coefficients"]})
                    continue
                nonexception_cases += 1
                per_cases += 1
                if witness is not None:
                    detail = direct_case(k, ell, t, s, gaussian_product)
                    require(detail["negative_first_differences"][0]["n"] == witness["n"],
                            "Direct first witness differs")
                    require(detail["negative_first_differences"][0]["first_difference"] == witness["first_difference"],
                            "Direct witness value differs")
                    failures.append({"k": k, "width": ell, "t": t, "shift": s,
                                     "m": k + ell, "b": k - 2 + t, **witness, **detail})
                    per_failures += 1
                    last_failure = ell
                    selected_cases.add((k, ell, t, s))
                db = differences(h, t)
                for n in range(ell + 1):
                    require(da[n] == hlarge[n], "Large edge identity failed")
                    u = n - s
                    if u >= 0:
                        require(u <= t, "Smaller Gaussian edge range failed")
                        require(db[u] == hsmall[u], "Small edge identity failed")
                        if s >= 2:
                            twos, threes = (s // 2, 0) if s % 2 == 0 else ((s - 3) // 2, 1)
                            require(twos >= 0 and 2 * twos + 3 * threes == s,
                                    "Injection's added partition has the wrong size")
                        require(hlarge[n] >= hsmall[u], "Edge injection inequality failed")
                    edge_checks += 1
        # Include the last observed failing width and its immediate neighbors.
        for ell in {last_failure - 1, last_failure, last_failure + 1}:
            if 1 <= ell <= args.max_width:
                parameters = admissible_by_t(k, ell)
                selected_cases.update((k, ell, t, s) for t, s in parameters[:2] + parameters[-2:])
        summary = {
            "k": k, "tested_widths": [1, args.max_width],
            "admissible_cases_excluding_shift_one": per_cases,
            "finite_failure_count": per_failures,
            "largest_failing_width_observed": last_failure,
            "m_corresponding_to_last_failure": k + last_failure if last_failure else None,
        }
        summaries.append(summary)
        print(json.dumps(summary, sort_keys=True), flush=True)

    require(primary_checks == expected_primary_checks, "Inspection-count reconstruction failed")
    require(edge_checks == expected_edge_checks, "Edge-count reconstruction failed")
    require(all_cases == nonexception_cases + len(exceptions), "Exception accounting failed")
    require(sum(x["finite_failure_count"] for x in summaries) == len(failures), "Failure accounting failed")

    spline_diagnostics = []
    for k in range(5, 13):
        for ell in (30, 90, 240):
            selected_pairs.add((k, ell))
            a = differences(k, ell)
            L = Fraction(2 * ell + k + 1, 2)
            points = sorted({ell, k * ell // 3, k * ell // 2 - 1, k * ell // 2})
            errors = [abs(Fraction(a[n]) - spline_main(k, ell, n)) / L ** (k - 4) for n in points]
            spline_diagnostics.append({"k": k, "width": ell, "points": points,
                                       "max_scaled_error": str(max(errors))})

    for k, ell, t, s in selected_cases:
        selected_pairs.update({(k, ell), (k - 2, t)})
    independent, pascal_states = gaussian_pascal_selected(selected_pairs)
    pair_records = []
    for r, w in sorted(selected_pairs):
        product, pascal = gaussian_product(r, w), independent[r, w]
        require(product == pascal, f"Product/q-Pascal mismatch at {(r, w)}")
        pair_records.append({"r": r, "width": w, "coefficient_count": len(product),
                             "coefficient_sha256": digest(product)})
    case_records = []
    for k, ell, t, s in sorted(selected_cases):
        detail = direct_case(k, ell, t, s, lambda r, w: independent[r, w])
        witness, _ = primary_check(k, ell, t, s)
        negatives = detail["negative_first_differences"]
        expected = None if not negatives else {key: negatives[0][key] for key in ("n", "first_difference")}
        require(expected == witness, "Independent direct-coefficient classification differs")
        if not negatives:
            require(detail["coefficient_minimum"] >= 0, "Passing symmetric difference has a negative coefficient")
        case_records.append({"k": k, "width": ell, "t": t, "shift": s,
                             "passed_nonnegative_unimodal_criterion": not negatives,
                             "first_negative_difference": expected,
                             "coefficient_sha256": detail["coefficient_sha256"]})

    algebra_records = half_shift_checks(max(args.max_k, 12))
    result = {
        "verifier_version": VERSION,
        "status": "Finite exact verification only; not an infinite theorem, threshold proof, or proof-assistant verification.",
        "range": {"min_k": 5, "max_k": args.max_k, "min_width": 1, "max_width": args.max_width,
                  "t": "0 <= t <= floor(k*width/(k-2)); k*width-(k-2)*t even"},
        "all_admissible_cases": all_cases,
        "admissible_cases_excluding_shift_one": nonexception_cases,
        "finite_failure_count_excluding_shift_one": len(failures),
        "passing_cases_excluding_shift_one": nonexception_cases - len(failures),
        "first_differences_inspected_including_exceptions": primary_checks,
        "first_difference_count_reconstructed_independently": expected_primary_checks,
        "exact_edge_identity_checks": edge_checks,
        "edge_check_count_reconstructed_independently": expected_edge_checks,
        "shift_one_cases_all_widths": len(exceptions),
        "shift_one_nonunimodality_checks_width_at_least_two": width_at_least_two_exceptions,
        "independent_parameter_rows_checked": parameter_rows,
        "parameter_stream_sha256": parameter_hash.hexdigest(),
        "legacy_grid_gaussian_cross_checks": len(base_pairs),
        "independent_gaussian_cross_checks_total": len(pair_records),
        "q_pascal_auxiliary_states_computed": pascal_states,
        "independent_full_polynomial_case_checks": len(case_records),
        "all_failing_tuples_independently_rechecked": len(failures),
        "all_negative_first_differences_in_failing_tuples": sum(len(f["negative_first_differences"]) for f in failures),
        "per_k": summaries,
        "spline_diagnostics": spline_diagnostics,
        "files": {"finite_failures": "finite_failures.json", "exception_witnesses": "exception_witnesses.json",
                  "independent_checks": "independent_checks.json", "runtime": "run_metadata.json"},
    }
    result["reference_comparison"] = compare_reference(result, failures, args.reference_results)
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    write_json(out / "verification_results.json", result)
    write_json(out / "finite_failures.json", failures)
    write_json(out / "exception_witnesses.json", exceptions)
    write_json(out / "independent_checks.json", {"gaussian_pairs": pair_records, "full_polynomial_cases": case_records,
                                                "half_shift_and_cancellation": algebra_records})
    fields = ("k", "width", "t", "shift", "m", "b", "n", "first_difference",
              "coefficient_minimum", "negative_coefficient_count")
    csv_stream = io.StringIO(newline="")
    writer = csv.DictWriter(csv_stream, fieldnames=fields, extrasaction="ignore", lineterminator="\n")
    writer.writeheader()
    writer.writerows(failures)
    (out / "finite_failures.csv").write_text(csv_stream.getvalue(), encoding="utf-8")
    data_files = ["verification_results.json", "finite_failures.json", "finite_failures.csv",
                  "exception_witnesses.json", "independent_checks.json"]
    hashes = {name: hashlib.sha256((out / name).read_bytes()).hexdigest() for name in data_files}
    source = Path(__file__).resolve()
    hashes["verify_sz.py"] = hashlib.sha256(source.read_bytes()).hexdigest()
    if args.reference_results.is_file():
        hashes[args.reference_results.name] = hashlib.sha256(args.reference_results.read_bytes()).hexdigest()
    write_json(out / "deterministic_sha256.json", hashes)
    metadata = {
        "started_utc": start_utc, "finished_utc": datetime.now(timezone.utc).isoformat(),
        "wall_seconds": round(time.perf_counter() - start_wall, 6),
        "cpu_seconds": round(time.process_time() - start_cpu, 6),
        "python_version": sys.version, "python_implementation": platform.python_implementation(),
        "platform": platform.platform(), "command": shlex.join(getattr(sys, "orig_argv", [sys.executable] + sys.argv)),
        "working_directory": str(Path.cwd()), "script_sha256": hashes["verify_sz.py"],
        "deterministic_file_sha256": hashes,
        "note": "Runtime metadata is intentionally excluded from deterministic output hashes.",
    }
    write_json(out / "run_metadata.json", metadata)
    print(json.dumps({"completed": True, "nonexception_cases": nonexception_cases,
                      "finite_failures": len(failures), "gaussian_cross_checks": len(pair_records),
                      "wall_seconds": metadata["wall_seconds"], "output_directory": str(out)}, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
