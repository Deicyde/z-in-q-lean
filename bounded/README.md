# The bounded polynomial implication

Run `lake build` in this directory with Lean 4.35.0. Lake uses the pinned upstream polynomial formalization and its dependencies. With a new package cache, `lake exe cache get` can download Mathlib’s compiled dependencies before the build. The root project has a separate dependency-free arithmetic library.

The theorem `ZOverQ.Bounded.bounded_from_height_tian_gross_zagier` takes three hypotheses.

| Hypothesis | Mathematical assertion |
| --- | --- |
| `ZInQ.SixContactMin` | The uniform six-contact height estimate for the genus-two family in the polynomial construction. |
| `PublishedTian47` | For the positive squarefree twists congruent to five modulo eight, oddness of either genus sum excludes a zero of order at least two. The formal equivalence with this analytic assertion is `tian_iff_orders`. |
| `SimpleZeroRank` | A rational elliptic curve whose arithmetic $`L`$-function has a simple zero at $`s=1`$ has a rational point of infinite order. |

The theorem `central_zero` supplies entire continuation and central vanishing from the Gaussian functional equation. The earlier declaration `bounded_from_height_and_literature` is also available with its original four arguments.

**Conclusion.** An integer polynomial in 292,890,231,905 total variables, with the degree and coefficient bounds of Glazer's Theorem 1.1, has rational projection exactly $`\mathbf Z`$. One variable is the input and 292,890,231,904 are rational witnesses. All three hypotheses appear in the Lean declaration. [Conditional theorem](BoundedFromGenus.lean) · [Exact target](https://github.com/elliotglazer/diophantine-z-q/blob/2358394558aafae202a1ce6d3bd1b536b79ad3d0/ZInQKernel/Target.lean)

**Genus calculation.** The second sum in Tian's statement has distinguished factors of residues $`5,7`$ and $`2,3`$, respectively. The other factors are $`1\bmod8`$. When the product is $`5\bmod8`$, the first two residues must be $`7,3`$. Squarefreeness ensures that the factors are distinct. Their multiset and set give the same weighted sum. The Lean proof identifies the integer sum with the class-group coefficient in the polynomial construction. The published normalization is zero at analytic order at least two. Oddness of the coefficient therefore excludes that order. Central vanishing gives a simple zero, and the rank hypothesis supplies precisely the rational point needed by the polynomial theorem. [Integer sum and proof](PublishedGenusRows.lean) · [Tian, §4.3 and Theorem 4.7, pp. 57–58](https://intlpress.com/site/pub/files/_fulltext/journals/iccm/2017/0005/0001/ICCM-2017-0005-0001-a003.pdf#page=7) · [Tian–Yuan–Zhang, original proof, p. 760](https://intlpress.com/site/pub/files/_fulltext/journals/ajm/2017/0021/0004/AJM-2017-0021-0004-a005.pdf#page=40) · [Upstream height-and-rank assembly](https://github.com/elliotglazer/diophantine-z-q/blob/2358394558aafae202a1ce6d3bd1b536b79ad3d0/ZInQKernel/RouteK/RankVariants.lean)
