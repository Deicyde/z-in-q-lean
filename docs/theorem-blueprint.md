# A proof blueprint for the bounded Diophantine definition

A subset of the rationals is **Diophantine over** $`\mathbb Q`$ if it is the set of first coordinates of the rational zeros of a polynomial with integer coefficients. For the integers, this asks for a polynomial $`P`$ such that every integer extends to a rational zero and every rational zero has integral first coordinate. The number of variables includes this first coordinate.

For the existence of a defining polynomial, the six-point height estimate may have an unspecified uniform coefficient. The Picard proof constructs the required bound on this scale from explicit statements on Prym varieties, isogenies, periods, reduction and rank. [Proof and literature inputs](qualitative-existence.md) · [Conditional Lean theorem](../Lean/Lemmas/picard-application/PicardConclusion.lean)

## 1. The theorem to be proved

Let $`N=292{,}890{,}231{,}905`$. Write $`T_1=2`$ and $`T_{k+1}=2^{T_k}`$, so that $`T_k`$ is a tower of $`k`$ twos. Glazer’s bounded assertion asks for an integer polynomial in $`N`$ variables of total degree less than $`T_7`$, with every coefficient of absolute value less than $`T_8`$, such that for every $`x\in\mathbb Q`$,

```math
x\in\mathbb Z
\quad\Longleftrightarrow\quad
\exists\,\mathbf y\in\mathbb Q^{N-1},\qquad P(x,\mathbf y)=0.
```

The bounds on $`P`$ are part of the conclusion. All the witnesses may depend on $`x`$; the polynomial is chosen once. [Exact bounded assertion](../Lean/Topics/theorem-blueprint/PublicAssembly.lean#L16)

**Theorem 1 (conditional reduction).** Assume the six-point height estimate of Section 2, the analytic consequence of Tian’s genus criterion in Section 3, and the positive-rank consequence of a simple central zero. Then the bounded assertion holds. Lean proves both directions of the displayed equivalence. The continuation of the selected elliptic curves’ arithmetic $`L`$-functions and their central vanishing follow from the Gaussian functional equation. [Bounded theorem and central vanishing](../bounded/BoundedFromGenus.lean) · [Glazer’s construction](https://github.com/elliotglazer/diophantine-z-q)

The Lake theorem takes an inequality for the rational parameter at one fixed set of exceptional primes. Section 2 states a sufficient inequality for the heights of the branch points of the sextic. The formal height comparison passes from the second inequality to the first. [Parameter-height statement](https://github.com/elliotglazer/diophantine-z-q/blob/2358394558aafae202a1ce6d3bd1b536b79ad3d0/ZInQKernel/Hypotheses/HeightMin.lean#L50) · [Application of the branch-height comparison](../Lean/Topics/original-rank/PublishedRankLeaves.lean#L21)

The height estimate bounds parameters that could otherwise give a nonintegral first coordinate. The rank argument supplies rational points of infinite order on the elliptic twists selected by the construction. These tasks concern different curves. They meet when the height and rank conclusions are substituted into the polynomial argument.

## 2. The height of six branch points

The parameter is a rational number $`u`$ outside the set

```math
D=\{0,-15,-20,-24,-30,-60\}.
```

Put $`F(u)=u(u+15)(u+20)(u+24)(u+30)(u+60)`$ and $`G(u)=7u^2+300u+3600`$. The invariant used to compare the family with the moduli of genus-two curves is

```math
j(u)=-\frac{57600F(u)^2}{G(u)^6}.
```

The polynomial $`G`$ is positive on the real line because its leading coefficient is positive and its discriminant is negative. [Parameter and invariant](../Lean/Topics/theorem-blueprint/HeightSix.lean)

**The curve.** Write $`u=a/b`$ in lowest terms with $`b\gt 0`$. Set $`m=3a(a+20b)(a+30b)`$, $`n=10(a+15b)(a+24b)(a+60b)`$ and $`t=n/m`$. The excluded values are exactly those where $`mn=0`$. With $`\alpha=X(X+3)`$, $`\beta=X+2`$ and $`\gamma=X^2+4X+6`$, put

```math
s_t(X)=\alpha^3-t\alpha\beta\gamma+t^2\beta^3.
```

Let $`\delta`$ be the product of the primes $`p\ge17`$ for which the valuation of the nonzero integer $`b^6F(a/b)`$ is $`2`$ modulo $`4`$. The curve $`C_u`$ is the smooth projective completion of $`y^2=-6\delta\,b^2G(a/b)m^2s_t(X)`$. This is the quadratic twist whose Jacobian occurs in the height argument. The six roots of $`s_t`$ are distinct, and the nonzero scalar in front of it leaves the branch points unchanged. [Integral equation](../Lean/Topics/marked-moduli/reduction/IntegralSextic.lean#L20) · [Choice of twist](../Lean/Topics/marked-moduli/twist/GlobalTwist.lean#L10) · [Smoothness](../Lean/Topics/marked-moduli/theta/SexticThetaHeight.lean#L17)

**Definition.** Order the six branch points and send the last one to infinity. Each partition into two triples determines a pair of the five finite roots and its complementary triple. Multiply the differences within the pair and within the triple, then square the product. There are $`\binom{6}{3}/2=10`$ partitions. The ten weights give a point of projective space. Write $`h_B(u)`$ for its normalized projective height. Dividing all coordinates by the first gives coordinates over the number field generated by their ratios. [Branch coordinates](../Lean/Topics/marked-moduli/branch-height/RationalBranchHeight.lean) · [Height normalization](../Lean/Lemmas/theta-quotient/ThetaQuotient.lean)

**Height hypothesis.** For every $`u\notin D`$ there is an ordering of the roots for which

```math
h_B(u)\leq 2^{26}\max\{1,\,6^{288}N(u)^{24}\}.
```

Here $`N(u)`$ is the product of the primes in the finite set `conductorPrimes` for this parameter. Its definition uses the fixed exceptional primes and the primes of odd contact with the six marked values. This explicit bound is sufficient for Theorem 1. [Quantifiers and field of definition](../Lean/Topics/marked-moduli/branch-height/CanonicalBranch.lean#L11) · [Prime product and constant](../Lean/Topics/marked-moduli/height/HeightBudget.lean#L65)

For a rational number $`a/b`$ in lowest terms with $`b\gt 0`$, let $`h(a/b)=\log\max\{|a|,b\}`$. Part of the geometric approach is a comparison between this elementary height and the stable Faltings height of the Jacobian $`A_u`$ of a specified quadratic twist:

```math
h(j(u))<30h_F(A_u)+150.
```

To see where the denominator enters, write $`j(u)=m/d`$ in lowest terms. In this family $`|j(u)|\lt 1`$, hence $`h(j(u))=\log d`$. A lower bound on the valuations of the minimal discriminant at primes dividing $`d`$ controls the finite term in the genus-two height formula. Bounds for the ten even theta constants control the archimedean term. Lean carries out the numerical deduction for the height and periods in the hypotheses. For any ordering of the branch points, the algebraic comparison gives $`h_B(u)\lt h(j(u))+175`$. Combining the two inequalities gives $`h_B(u)\lt 30h_F(A_u)+325`$. The effective bound $`h_F(A_u)\le 6^{288}N(u)^{24}`$ would now imply the displayed height hypothesis, since $`355\lt 2^{26}`$. Both height theorems must be applied to the same Jacobian. In genus two the metric convention in the global formula contributes $`+\log\pi`$ when expressed in the normalization of the effective bound. [Branch-height comparison](../Lean/Topics/marked-moduli/jacobian-height/ModularBranchHeight.lean#L19) · [von Känel, Theorem 6.2](https://doi.org/10.1017/fms.2021.29) [Discriminant inequality](../Lean/Topics/marked-moduli/quaternion-marking/theta-class/minimal-discriminant/IntegralDiscriminant.lean) · [Height theorem](../Lean/Topics/marked-moduli/quaternion-marking/theta-class/minimal-discriminant/GlobalHeight.lean#L35) · [Habegger–Pazuki](https://doi.org/10.1112/S0010437X17007424)

## 3. Rational points on the selected elliptic twists

For a positive squarefree $`d\equiv5\pmod 8`$, let $`E_d`$ be the elliptic curve $`y^2=x^3-d^2x`$. The argument selects $`d`$ by a parity test. Write $`B(d)`$ for the second genus coefficient in the proof of Tian–Yuan–Zhang’s Theorem 3.5(2). Its terms correspond to unordered factorizations of $`d`$ into integers greater than one. In this coefficient one factor is $`7`$ modulo $`8`$, one is $`3`$ modulo $`8`$, and the others are $`1`$ modulo $`8`$. For a factor $`e`$, put $`g(e)=\#(2\,\mathrm{Cl}(\mathbb Q(\sqrt{-e})))`$, the order of the subgroup of doubles in the ideal class group. Each factorization contributes the product of these weights. Ye Tian’s Theorem 4.7 states the two genus criteria separately. [Tian, Theorem 4.7](https://intlpress.com/site/pub/files/_fulltext/journals/iccm/2017/0005/0001/ICCM-2017-0005-0001-a003.pdf#page=8) [Coefficient and curve conventions](../Lean/Topics/original-rank/PrintedTwistModel.lean) · [Tian–Yuan–Zhang, p. 760](https://web.math.princeton.edu/~shouwu/publications/cn.pdf#page=40)

**Lemma 2 (rank from parity).** Assume the following two implications for the normalized $`L`$-function used here.

1. If it has order of vanishing greater than one at $`s=1`$, then $`B(d)`$ is even.
2. A modular elliptic curve with a simple zero at $`s=1`$ has a rational point of infinite order.

Then every selected $`d`$ with $`B(d)`$ odd gives an elliptic curve $`E_d`$ of positive rational rank.

**Proof.** The functional equation gives $`L(E_d,1)=0`$ for these twists. Since the first implication excludes order at least two, the central zero is simple. The second implication supplies a point of infinite order. For the coefficient comparison, an unordered factorization is a multiset. No factor greater than one can repeat in a squarefree product, since the square of any prime dividing the repeated factor would divide the product. Passing to the set of factors therefore preserves each class-group weight and its contribution to the sum. [Lean proof of the weighted identity](../bounded/TYZMultisetWeights.lean) · [Rank deduction](../bounded/BoundedFromGenus.lean) · [Gross–Zagier, Chapter I, Theorem 7.3](https://people.mpim-bonn.mpg.de/zagier/files/doi/10.1007/BF01388809/fulltext.pdf#page=7)

The Lean hypothesis for Tian’s theorem records the analytic consequence used here. It is equivalent to excluding order at least two when either of the two genus sums is odd. Tian’s definitions of the isogeny index and the lower-order special values supply one choice for the existential quantities in that hypothesis. [Equivalence of the two statements](../bounded/BoundedFromGenus.lean)

## 4. What remains for the geometric proof

The Jacobian of a genus-two curve is a principally polarized abelian surface. The polarization is required here because the argument concerns an endomorphism attached to a *marked* surface. A marking specifies the action in question. Knowing the weighted Igusa coordinates identifies a candidate geometric isomorphism class. One must still transport the specified endomorphism to the actual Jacobian and determine its field of definition.

| Mathematical step | Deduction available in Lean | Remaining input in this route |
| --- | --- | --- |
| Identify the surface | Compute the weighted Igusa coordinates of the signed sextic and compare them with the discriminant-six family. | Interpret that equality on the polarized moduli space and identify the marked representative at the given rational parameter. [Invariants](../Lean/Lemmas/six-raw-jacobian/igusa/algebraic-class/SixPolarizedIgusa.lean) · [Baba–Granath](https://doi.org/10.4153/CJM-2008-033-7) |
| Descend the endomorphism | A compatible marked action and a scalar ambiguity give the same distinguished real endomorphism after conjugation. | Supply the marking, its polarization and its forgetful map on one surface. [Marked action](../Lean/Lemmas/six-quaternion-lift/SixPolarizedTransport.lean) |
| Control bad reduction | Compute root collisions and valuations on the signed sextic. | Apply the reduction criteria to its Jacobian over the field used for the height calculation. [Local computation](../Lean/Topics/marked-moduli/reduction-application/RationalReduction.lean) · [Cluster criterion](https://doi.org/10.1007/s00208-021-02319-y) |
| Compare the two heights | Deduce the explicit inequality of Section 2 from the finite and archimedean terms. | Identify one stable Faltings height, with its normalization, in the global formula and in the effective bound for an abelian surface with real multiplication. [Height formula in Lean](../Lean/Topics/marked-moduli/quaternion-marking/theta-class/minimal-discriminant/GlobalHeight.lean#L21) · [Effective surface bound](../Lean/Topics/marked-moduli/jacobian-height/JacobianDiscriminant.lean) |

**Lemma 3 (the Torelli sign).** Suppose the pointed determinant induces the canonical polarization and the general Weierstrass coordinate formula applies. Every polarized automorphism of the signed Jacobian acts as the identity or its negative. Indeed, subtracting two Abel images cancels the translation in strong Torelli. The hyperelliptic involution reverses the sign of their difference. The coordinate action on the signed curve fixes the remaining ambiguity, including at the points at infinity. This identifies the action once the ordinary marked representative has been supplied. [Scalarity on the signed Jacobian](../Lean/Lemmas/ordinary-abel-comparison/PolarizedAbelAction.lean) · [Geometric implication](../Lean/Lemmas/ordinary-abel-comparison/OrdinaryPolarizedEndpoint.lean) · [Geometric and rank inputs in one theorem](../Lean/Lemmas/ordinary-abel-comparison/literature/OrdinaryHeightAndRank.lean)

The CM computation excludes the 27 numerical coordinates in Errthum’s table. One still has to identify the arithmetic coordinate of the represented Jacobian with the coordinate used in the complete rational CM classification. The height argument also requires a single stable Faltings height with the normalization in Section 2. [Exclusion of the tabulated values](../Lean/Lemmas/six-quaternion-lift/SixRationalCM.lean) · [Comparison at the two CM fields](../Lean/Lemmas/cm-order-repair/CMFieldRows.lean)

## 5. Other polynomial bounds

A polynomial can be reduced in size by proving that two systems have the same first-coordinate projection over $`\mathbb Q`$. The 85-variable construction establishes such an equality for a particular 222-coordinate family, uniformly in its coefficient. To use it as a definition of the integers one must also identify that family’s projection with $`\mathbb Z`$. The first version of Sun’s preprint gives a different construction with 28 witnesses. It shares arithmetic ideas with the earlier work and has its own remaining hypotheses. [Compression theorem](variable-bound.md) · [Sun’s construction and outstanding estimates](sun-28.md) · [Results by construction](results.md)
