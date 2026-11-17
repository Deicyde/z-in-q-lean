# The bounded polynomial implication

Run `lake build` in this directory with Lean 4.35.0. Lake uses the pinned upstream polynomial formalization and its dependencies. With a new package cache, `lake exe cache get` can download Mathlib’s compiled dependencies before the build. The root project has a separate dependency-free arithmetic library.

The theorem `ZOverQ.Bounded.bounded_from_height_and_literature` takes four hypotheses.

| Hypothesis | Mathematical assertion |
| --- | --- |
| `ZInQ.SixContactMin` | The six-contact height estimate in the pinned polynomial construction. |
| `PublishedTian47` | The two genus criteria in Ye Tian's Theorem 4.7, restricted to positive squarefree twists of residue five modulo eight. |
| `CentralZero` | The arithmetic Hasse–Weil series of each such twist has an entire continuation vanishing at the centre $`s=1`$. |
| `SimpleZeroRank` | A rational elliptic curve with a simple zero at $`s=1`$ has a rational point of infinite order. |

**Conclusion.** An integer polynomial in 292,890,231,905 total variables, with the degree and coefficient bounds of Glazer's Theorem 1.1, has rational projection exactly $`\mathbf Z`$. One variable is the input and 292,890,231,904 are rational witnesses. All four hypotheses appear in the Lean declaration. [Conditional theorem](BoundedFromGenus.lean) · [Exact target](https://github.com/elliotglazer/diophantine-z-q/blob/eef7deb0317c2120956d27f2be1bc06cb5c8e5ba/ZInQKernel/Target.lean)

**Genus calculation.** The second sum in Tian's statement has distinguished factors of residues $`5,7`$ and $`2,3`$, respectively. The other factors are $`1\bmod8`$. When the product is $`5\bmod8`$, the first two residues must be $`7,3`$. The Lean proof identifies the integer sum with the class-group coefficient in the polynomial construction. The published normalization is zero at analytic order at least two. Oddness of the coefficient therefore excludes that order. Central vanishing gives a simple zero, and the rank hypothesis supplies precisely the rational point needed by the polynomial theorem. [Integer sum and proof](PublishedGenusRows.lean) · [Tian, §4.3 and Theorem 4.7, pp. 57–58](https://intlpress.com/site/pub/files/_fulltext/journals/iccm/2017/0005/0001/ICCM-2017-0005-0001-a003.pdf#page=7) · [Tian–Yuan–Zhang, original proof, p. 760](https://intlpress.com/site/pub/files/_fulltext/journals/ajm/2017/0021/0004/AJM-2017-0021-0004-a005.pdf#page=40) · [Upstream height-and-rank assembly](https://github.com/elliotglazer/diophantine-z-q/blob/eef7deb0317c2120956d27f2be1bc06cb5c8e5ba/ZInQKernel/RouteK/RankVariants.lean)
