# Stanley–Zanello Conjecture 1.1(iv)

For every fixed integer height k ≥ 5 and all sufficiently large upper indices m, the centered difference of Gaussian polynomials in [Stanley and Zanello’s Conjecture 1.1(iv)](https://arxiv.org/abs/1711.10033) has nonnegative, unimodal coefficients for every admissible b except the shift-one case. The threshold depends only on k. The proof combines an edge injection with a uniform first-difference estimate obtained by averaging shifted restricted-partition counts over subsets of fixed cardinality.

[Paper (PDF)](paper/Stanley-Zanello-Final.pdf) · [Main theorem](lean/SZ/Original.lean) · [Axiom audit](certificates/axioms.log)

## Reproduce

Install Elan, Git and Python 3. From the repository root run:

```sh
(cd lean && bash verify.sh)
python3 verification/verify_sz.py --output-dir scan-results
shasum -a 256 -c SHA256SUMS
```

Lean 4.24.0 and Mathlib v4.24.0 (f897ebcf72cd16f89ab4577d0c826cd14afaafc7) are pinned. The script builds the library and audits fourteen declarations. The transitive axioms of `SZ.original_conjecture` are `propext`, `Classical.choice` and `Quot.sound`. The finite scan checks bounded parameter ranges independently.

## Author

Felix Dongting Fei · [Author contributions and AI disclosure](paper/Stanley-Zanello-Final.pdf#page=8)

## Licensing

Project software and software documentation are MIT licensed. The paper, LaTeX sources, verification data and audit certificates are licensed under CC BY 4.0. See the [scope of the licenses](LICENSE), the [MIT license](lean/LICENSE) and the [CC BY 4.0 license](licenses/CC-BY-4.0.txt).
