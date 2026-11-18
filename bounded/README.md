# Two polynomial definitions under height and rank hypotheses

Run `lake build` in this directory with Lean 4.35.0. Lake uses the pinned upstream polynomial formalization and its dependencies. With a new package cache, `lake exe cache get` can download Mathlib’s compiled dependencies before the build. The root project has a separate dependency-free arithmetic library.

### Existence with an unspecified constant

The theorem `integer_polynomial_of_uniform_height` constructs a natural number of witnesses and an integer polynomial whose rational solutions project exactly to the ordinary integers. Its hypotheses are a uniform six-contact estimate with any real coefficient, Tian’s genus criterion, and positive rational rank at a simple central zero. The finite cutoff depends on the coefficient. [Theorem and definition of the target](IntegerPolynomial.lean)

| Part of the proof | Lean result |
| --- | --- |
| Multiplication on point codes | An adjustable cutoff excludes every false multiplication. [Proof](QualitativeMultiplication.lean) |
| Recovery of the ordinary integer | The local test at one shift and precision at a fixed multiple characterize all nonexceptional integers. [Proof](QualitativePrecision.lean) |
| One polynomial | All auxiliary variables are existential. A sum of squares joins the tests and a product includes the six exceptional values. [Finite polynomial relations](FinitePolynomial.lean) · [Assembly](IntegerPolynomial.lean) |
| Six-contact height | Odd branch valuations, finite exceptional sets, the rational-root height estimate for the sextic invariant, and the exponent 24 in the numerical Shafarevich bound are proved. [Branch form](QualitativeHeight.lean) · [Sextic computation](PicardSextic.lean) · [Height comparison](ModuliHeight.lean) |
| Local roots and conjugate charts | The two local calculations determine the six roots and their differences for every residue characteristic greater than three. An explicit isomorphism identifies the twisted sextic with its conjugate on the affine and reciprocal charts. [Hensel lifting](PicardLocal.lean) · [Change of coordinates](PicardConjugation.lean) |
| Geometric application | The remaining inputs are good-reduction support and the effective and moduli height estimates on the same family of fibres. The final Lean theorem displays each input. [Family criterion](PicardCriterion.lean) |

### Glazer’s prescribed polynomial

The theorem `ZOverQ.Bounded.bounded_from_height_tian_gross_zagier` takes three hypotheses.

| Hypothesis | Mathematical assertion |
| --- | --- |
| `ZInQ.SixContactMin` | The uniform six-contact height estimate for the genus-two family in the polynomial construction. |
| `PublishedTian47` | For the positive squarefree twists congruent to five modulo eight, oddness of either genus sum excludes a zero of order at least two. The formal equivalence with this analytic assertion is `tian_iff_orders`. |
| `SimpleZeroRank` | A rational elliptic curve whose arithmetic $`L`$-function has a simple zero at $`s=1`$ has a rational point of infinite order. |

The theorem `central_zero` supplies entire continuation and central vanishing from the Gaussian functional equation. The earlier declaration `bounded_from_height_and_literature` is also available with its original four arguments.

**Conclusion.** An integer polynomial in 292,890,231,905 total variables, with the degree and coefficient bounds of Glazer's Theorem 1.1, has rational projection exactly $`\mathbf Z`$. One variable is the input and 292,890,231,904 are rational witnesses. All three hypotheses appear in the Lean declaration. [Conditional theorem](BoundedFromGenus.lean) · [Exact target](https://github.com/elliotglazer/diophantine-z-q/blob/2358394558aafae202a1ce6d3bd1b536b79ad3d0/ZInQKernel/Target.lean)

**Genus calculation.** The second sum in Tian's statement has distinguished factors of residues $`5,7`$ and $`2,3`$, respectively. The other factors are $`1\bmod8`$. When the product is $`5\bmod8`$, the first two residues must be $`7,3`$. Squarefreeness ensures that the factors are distinct. Their multiset and set give the same weighted sum. The Lean proof identifies the integer sum with the class-group coefficient in the polynomial construction. The published normalization is zero at analytic order at least two. Oddness of the coefficient therefore excludes that order. Central vanishing gives a simple zero, and the rank hypothesis supplies precisely the rational point needed by the polynomial theorem. [Integer sum and proof](PublishedGenusRows.lean) · [Tian, §4.3 and Theorem 4.7, pp. 57–58](https://intlpress.com/site/pub/files/_fulltext/journals/iccm/2017/0005/0001/ICCM-2017-0005-0001-a003.pdf#page=7) · [Tian–Yuan–Zhang, original proof, p. 760](https://intlpress.com/site/pub/files/_fulltext/journals/ajm/2017/0021/0004/AJM-2017-0021-0004-a005.pdf#page=40) · [Upstream height-and-rank assembly](https://github.com/elliotglazer/diophantine-z-q/blob/2358394558aafae202a1ce6d3bd1b536b79ad3d0/ZInQKernel/RouteK/RankVariants.lean)

For the subsequent arithmetic, the Picard package derives the prime support from the branch polynomial and proves the normalized theta-height comparison. Its endpoint displays the rational abelian factor still to be constructed. [Picard application](../picard/README.md)
