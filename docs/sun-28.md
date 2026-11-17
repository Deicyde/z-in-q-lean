# Sun’s construction with 28 rational witnesses

Theorem 1.1 of the first version of Sun’s preprint proposes a polynomial $`P`$ over the integers with one input $`x`$ and 28 rational witnesses. Its assertion is that

```math
x\in\mathbb Z
\quad\Longleftrightarrow\quad
\exists\,\mathbf w\in\mathbb Q^{28},\quad P(x,\mathbf w)=0
\qquad (x\in\mathbb Q).
```

Thus the polynomial has 29 variables in total. This is the same qualitative Diophantine assertion as Glazer’s, with a different polynomial and different arithmetic hypotheses. The variable count alone gives no corresponding bound on the degree. [Sun, Theorem 1.1](https://arxiv.org/abs/2611.14605v1) · [Glazer’s bounded theorem](theorem-blueprint.md)

The second version, dated 13 November 2026, announces 26 witnesses, or 27 total variables. The Lean theorem examined here quantifies over 28 witnesses and concerns the first version. [Sun, second version](https://arxiv.org/abs/2611.14605v2)

## From a rational zero to an integer

Given a rational zero, the equations impose divisibility conditions on indices of multiples of elliptic points. At primes where the parameter meets a marked value to odd order, the formal group of the elliptic curve turns the local conditions into congruences on the indices. The remaining argument compares the resulting lower bounds with heights. [Index and residue calculations](../Lean/Topics/multiple-residues/) · [Formal polynomial implication](../Lean/Topics/sun-28/scalar-height/weighted/ExceptionalProjection.lean#L57)

One comparison involves the height of $`\beta=2x^2+3`$. At primes greater than 76,176, the relevant prime product detects odd valuations of

```math
(2x^2+3)(x^2+1)(x^2-1199)(64x^2+439).
```

With $`x=a/b`$ in lowest terms, let $`E(B)`$ count the exceptional inputs of height $`\max(|a|,b)\le B`$ in the stated scalar estimate. The proved density bound gives $`E(B)/B^2\to0`$. A nonintegral rational zero of $`P`$ could still lie in this exceptional set. The conditional proof therefore retains a height estimate for the exceptional inputs that actually satisfy the polynomial constraints. There is a further estimate on the ordinary elliptic components. [Exceptional set](../Lean/Topics/sun-28/scalar-height/weighted/InputDensity.lean) · [Exact remaining estimates](../Lean/Topics/sun-28/scalar-height/weighted/ExceptionalProjection.lean#L24)

## From an integer to a rational zero

For an integer input, the problem is to construct a single tuple of rational witnesses. There are two distinct choices to make.

1. **Primes with prescribed local conditions.** The prime choices must satisfy several congruences and exclusion conditions at once. The proposed argument combines a lower bound for prime values in a Gaussian ideal class with an upper bound for unwanted configurations. The estimates have to hold for the ranges used by the polynomial. [Prime-value problem](../Lean/Topics/sun-28/ray-density/prime-transfer/FixedClass.lean)
2. **Simultaneous rational points.** Several elliptic conditions share a parameter. Existence of a rational point for each condition at its own parameter is insufficient. For the companion curve $`y^2=x(x-\ell)(x+3\ell)`$ one needs a point with $`y\ne0`$ and a prescribed square class of $`x`$, together with the point required on the other twist. Descent gives explicit intersections of quadrics for an individual parameter. Uniform existence with a common parameter remains open in the formalization. [Descent to quadrics](../Lean/Topics/sun-28/global-descent/common-pair/squareclass-pencil/AbscissaQuartic.lean)

## The conditional theorem in Lean

The formal theorem applies to the fixed polynomial itself. Its arguments include the residual height estimates, the prime-value estimates and the simultaneous-point hypothesis, as well as stated inputs about real elliptic curves, quadratic forms and units. From these hypotheses Lean proves both implications for every rational $`x`$. Each use of a literature result must still match the objects and ranges in its Lean statement. [Theorem and hypotheses](../Lean/Topics/sun-28/scalar-height/weighted/ExceptionalProjection.lean#L57) · [Five marked points](../Lean/Topics/sun-28/) · [Pointwise height comparisons](../Lean/Topics/sun-28/scalar-height/)
