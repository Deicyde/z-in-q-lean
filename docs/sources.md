# Sources and conventions

The bounded polynomial construction and the upstream Lean development are the work of the **ℤℚ Diophantine Project contributors**. The separate Lake project in `bounded/` imports their development at a fixed revision. The accompanying sources study reductions of its hypotheses and compare later polynomial presentations. The variable counts always include the input unless explicitly described as numbers of witnesses. [Upstream development](https://github.com/elliotglazer/diophantine-z-q/tree/eef7deb0317c2120956d27f2be1bc06cb5c8e5ba) · [Package manifest](../bounded/lake-manifest.json)

| Mathematical subject | Source and use |
| --- | --- |
| Quaternionic multiplication on genus-two curves | Baba and Granath describe the discriminant-six family and its moduli. The marked comparison for the particular signed Jacobian is an explicit hypothesis. [Baba–Granath](https://doi.org/10.4153/CJM-2008-033-7) |
| Stable Faltings height | The geometric route needs Habegger and Pazuki’s genus-two height formula and von Känel’s effective estimate in compatible normalizations. [Height formula](https://doi.org/10.1112/S0010437X17007424) · [Effective estimate](https://doi.org/10.1017/fms.2021.29) |
| Genus coefficients of congruent-number curves | Ye Tian’s Theorem 4.7 gives two criteria in terms of products of class-group orders. The Lean comparison matches the second coefficient to the one needed on the selected twists. [Tian, Theorem 4.7](https://intlpress.com/site/pub/files/_fulltext/journals/iccm/2017/0005/0001/ICCM-2017-0005-0001-a003.pdf#page=8) · [Formal hypotheses](../bounded/README.md) |
| Rank from a simple zero | Gross and Zagier relate derivatives of the relevant modular $L$-functions to heights of Heegner points. The bounded implication lists its positive-rank input explicitly. [Gross–Zagier](https://people.mpim-bonn.mpg.de/zagier/files/doi/10.1007/BF01388809/fulltext.pdf#page=7) |
| Variable bounds with unrestricted degree | The 28-witness declarations follow the first version of Zhi-Wei Sun’s preprint. The second version announces 26 witnesses. [Version 1](https://arxiv.org/abs/2611.14605v1) · [Version 2](https://arxiv.org/abs/2611.14605v2) |

The directory guides link to theorems used in a particular proof. The Lean sources retain their original mathematical names. Standard library dependencies for the two build targets are specified in their Lake manifests. [Mathlib](https://github.com/leanprover-community/mathlib4) · [Root package](../lakefile.toml)
