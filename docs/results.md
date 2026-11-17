# Results and hypotheses

Three different questions occur in the polynomial constructions. The first asks whether a polynomial defines $`\mathbb Z`$ inside $`\mathbb Q`$. The second asks whether two polynomial systems have the same rational image. The third asks how many coordinates are needed to express that image. An answer to one of the last two questions can be used before the first has been settled.

## Statements by construction

| Construction | Result established | Mathematical work remaining |
| --- | --- | --- |
| Glazer’s bounded construction | Lean deduces the full degree, coefficient and variable bounds and the characterization of the integers from an intrinsic genus-two height estimate and two elliptic rank implications. | Supply the exact height and rank statements. The proposed geometric argument for the height estimate includes an identification on a marked Jacobian. [Proof blueprint](theorem-blueprint.md) |
| The 222-coordinate quartic family | A uniform polynomial in 85 total variables preserves the rational projection for every rational coefficient. For nonzero coefficients a second construction uses 67. Fixing the coefficient saves one variable in each case. | Identifying the projection with $`\mathbb Z`$ requires the arithmetic theorem for the chosen coefficient. The source-table identifications have written proofs and computational verification. [Compression and its formal scope](variable-bound.md) |
| Sun’s first version (28 witnesses) | Lean derives the asserted equivalence for a fixed polynomial with 29 total variables under explicit hypotheses. | Prove the remaining height estimates, the simultaneous prime estimates and the existence of rational points with a common parameter. [Sun’s argument](sun-28.md) |

## Independently usable deductions

- **Branch coordinates and reduction.** For the signed sextic one can compute the weighted Igusa invariants and the valuations of differences of roots. These are inputs to the identification and reduction of its Jacobian. [Invariants](../Lean/Lemmas/six-raw-jacobian/igusa/SixIgusaTuple.lean) · [Local reduction](../Lean/Topics/marked-moduli/reduction-application/RationalReduction.lean)
- **Genus coefficients and elliptic rank.** For the selected congruent-number twists, parity and the functional equation reduce positive rank to the modular simple-zero criterion. The proof identifies the equations and the normalized $`L`$-functions used on both sides. [Rank reduction](../Lean/Topics/original-rank/PrintedRankEndpoint.lean#L8)
- **Elimination over the rationals.** A finite system of monic equations may admit rational values for coordinates coming from different algebraic solutions. Separating the tuples before taking a rational witness preserves the projection after specialization. [One-witness argument](variable-bound.md#why-a-single-additional-witness-suffices)

The formalization dashboard gives chapter totals and links to individual mathematical statements. [Formalization dashboard](../README.md#formalization-dashboard) · [Index of mathematical statements](../dashboard/README.md)
