# Prior art

The README makes a priority claim: to our knowledge, F4 is the first machine-checked computation of the intrinsic box-covering dimension of a recursively growing family of finite combinatorial graphs. This page records the search behind that claim, so it can be checked and corrected.

## The claim, exactly

- **What is claimed:** the first machine-checked computation, in any proof assistant, of the box-covering dimension of a recursively growing family of **finite combinatorial graphs**. Boxes are vertex sets of intrinsic (graph-distance) diameter less than \(\ell\), in the Song–Havlin–Makse sense, and the limit is taken along every admissible scale sequence.
- **What is not claimed:**
    - that the value \(\log(u+v)/\log u\) is new;
    - that this is the first proof of it, informal or rigorous;
    - that it is the first formal computation of a fractal dimension of any object;
    - that it is a formalized renormalization-group argument. The proof uses the flowers' exact self-similar decomposition, not a renormalization flow.

## Search

- **Date:** 27 September 2026.
- **Proof assistants and libraries:**
    - Lean 4: Mathlib, and public GitHub repositories found by keyword.
    - Isabelle: the Archive of Formal Proofs and its GitHub mirror.
    - Rocq/Coq, Mizar (the MML), HOL Light and Metamath.
    - arXiv, for papers on formalized fractal dimension.
- **Terms:** box-counting, box-covering, Minkowski, Hausdorff and fractal dimension, combined with formalization, Lean, Isabelle, Coq and Mizar. Also `dimH`, `cantorSet`, Sierpinski, self-similar, iterated function system, renormalization, decimation, hierarchical lattice and Migdal–Kadanoff.
- **Not accessed:**
    - the Lean Zulip archive, which our search tools do not index;
    - some GitHub code searches, which hit rate limits;
    - several paywalled papers, listed below.

## What was found

**Informal and paper results on the flowers**

- Rozenfeld, Havlin & ben-Avraham, *New J. Phys.* 9, 175 (2007). They obtain \(d_B = \ln(u+v)/\ln u\) from the flowers' self-similar scaling: vertices multiply by \(u+v\) and lengths by \(u\). This is a scaling argument, not a bound on minimum box covers at every scale.
- Z. Neroli, "Fractal dimensions for iterated graph systems", *Proc. R. Soc. A* 480, 20240406 (2024), [doi:10.1098/rspa.2024.0406](https://doi.org/10.1098/rspa.2024.0406). The arXiv version, 2212.01987, lists the author as Nero Ziyu Li.
    - It proves explicit Minkowski- and Hausdorff-dimension formulae for deterministic iterated graph systems.
    - Its statement concerns a Gromov–Hausdorff scaling limit, not minimum box covers of the finite graphs.
    - The flowers appear to fit its framework as a one-colour system, but the paper does not treat them. The specialization and the bridge between the two definitions have not been written down, so we describe F4 as consistent with this theorem, not as following from it.
- Xi et al., *Physica A* 478 (2017), and Li–Yao–Wang, *Physica A* 525 (2019), on substitution networks. Paywalled; not checked.

**Formal results on fractal dimension (none on graph families)**

- [rwst/lean-code](https://github.com/rwst/lean-code), outside Mathlib: `BB61/BoxDim.lean` and `BB61/Hausdorff.lean`, committed 15 September 2026. They prove the box and Hausdorff dimension of a Cantor-set family, which includes the middle-thirds set. These are fractal sets in \(\mathbb{R}\), not graphs.
- [itakura-hidetoshi/KuuOS](https://github.com/itakura-hidetoshi/KuuOS), outside Mathlib, dated 26 September 2026. It proves that Mathlib's `cantorSet` has Hausdorff dimension \(\log_3 2\).
- Principia-Fractalis (Lean) proves an upper bound on the Cantor set's Hausdorff dimension only.
- Mathlib defines Hausdorff dimension and covering numbers, and computes integer dimensions such as those of \(\mathbb{R}^n\). It has no box dimension for graphs.
- [hsfn-lean](https://github.com/Tongji708A/hsfn-lean) formalizes the combinatorics of a fractal network (degrees, distances, diameter), but no dimension.
- A Rocq/Coq hyperspace formalization ([arXiv 2410.13508](https://arxiv.org/abs/2410.13508)) constructs the Sierpinski triangle, but proves no dimension.
- The Isabelle AFP, Mizar, HOL Light and Metamath turned up no fractal-dimension results.

**Formal results on renormalization**

- [hawkrobe/linglib](https://github.com/hawkrobe/linglib) formalizes Birkhoff factorization for Connes–Kreimer renormalization, in the QFT sense.
- No formalization of renormalization-group, decimation, hierarchical-lattice or Feigenbaum renormalization was found. Lanford's Feigenbaum proof is computer-assisted (interval arithmetic), not a proof-assistant formalization.

## Corrections

A search cannot prove that nothing exists. If you know of an earlier formal proof of the box-covering dimension of a graph family, in any proof assistant, please [open an issue](https://github.com/Project-Navi/fd-formalization/issues). We will correct the claim.
