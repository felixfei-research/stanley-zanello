# Stanley–Zanello Conjecture 1.1(iv)

`SZ.original_conjecture` in `SZ/Original.lean` is the result in integer variables. It uses the usual upper and lower indices, the actual polynomial degree and the printed exponent. The conjunction of nonnegativity of every coefficient and unimodality holds exactly away from the stated exception. `SZ.exception_not_unimodal` proves the stronger failure of unimodality itself for every admissible shift one.

## Reproduce

Install Elan, Git and Python 3, extract the source tree to a new directory, and run from that directory:

```sh
bash verify.sh
```

Elan reads `lean-toolchain` (Lean 4.24.0). Lake reads the committed manifest. Mathlib is pinned to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. The first invocation requires network access for the compiler, Git dependencies and matching Mathlib cache. The project source is compiled locally. The script checks the printed axiom dependencies and exits nonzero on a build or audit failure.

With the pinned dependencies and their compiled cache already installed, the two essential commands are:

```sh
lake build
lake env lean Audit.lean
```

To also isolate the compiler and cache on a second run, extract into another empty directory, export `ELAN_HOME` and `XDG_CACHE_HOME` to new paths, and run the same script using the Elan proxies. All project modules must be built from source in that directory. The distribution contains no project .olean files.

## Reading the proof

| Module under SZ/ | Mathematical content |
|---|---|
| Gaussian | q-Pascal recursion, denominator-cleared product formula, second recursion, all-index symmetry and initial coefficients |
| Statement, Original | Integer admissibility, parity, threshold conversion, exception, equality of the actual polynomials and the effect of trimming terminal zeros |
| Shape | Failure at shift one and the left-half criterion for a peak at the center |
| Series, Comparison | Restricted generating series, uniform smaller-polynomial bound, nonnegative edge coefficients |
| Partitions | Coefficients of the restricted series equal counts of finite multiplicity vectors |
| Base, Lift, Main | Height-five rational generating identity, centered finite-difference induction, all-integer restricted estimate |
| Spline | Truncated powers, spline derivative recursion, positivity and strict negative curvature, compact linear lower bound |
| Averaging | Reflection within each subset cardinality, derivatives of the perturbation, uniform quadratic error |
| Expansion, Uniform, Estimates | Exact Gaussian coefficient expansion, all scaling identities, uniform approximation and bulk lower bound |
| Reduction | Uniform comparison with the smaller polynomial and conclusion in both parameterizations |

Only the three standard Lean foundations `propext`, `Classical.choice` and `Quot.sound` occur in the reported transitive dependencies of the final theorem. The finite Python scan is independent of the Lean project.
