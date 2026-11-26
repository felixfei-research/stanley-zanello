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

## Author and contributions

Felix Dongting Fei, Independent Researcher · [ORCID](https://orcid.org/0009-0000-8891-7101) · felix.d.fei@gmail.com

The author initiated and directed the research, set the problem-selection criteria, designed the verification workflow, and evaluated and integrated the results. GPT-6 Pro (OpenAI, via ChatGPT) selected the conjecture, developed the proof and wrote initial verification code. GPT-6.2 Astra (OpenAI, via Codex) audited the argument, developed the Lean formalization and alternative algebraic restricted-partition proof, and performed computational verification. Both models contributed to the manuscript. Additional model runs checked the arguments and literature. The author assumes responsibility for the manuscript and submission.

## Licensing

Project software and software documentation are MIT licensed. The paper, LaTeX sources, verification data and audit certificates are licensed under CC BY 4.0. See the [scope of the licenses](LICENSE), the [MIT license](lean/LICENSE) and the [CC BY 4.0 license](licenses/CC-BY-4.0.txt).
