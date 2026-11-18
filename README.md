# Can one polynomial recognize the integers among the rationals?

Give the polynomial a rational number as its first input. Can you fill its remaining inputs with rational numbers so that the answer is zero? We want a single polynomial for which this is possible for every integer, including negative integers and zero, and impossible for every other fraction. For example, 3 must admit a solution and 3/2 must admit none.

**What Lean proves.** Assuming twelve stated results from arithmetic and geometry, such a polynomial exists. Lean checks the deduction from those hypotheses to the conclusion. Several hypotheses require matching the curves, maps or heights in a published theorem with the ones used here. Those identifications remain part of the assumptions. The result gives no numerical bound on the number of variables. [Final theorem in Lean](Lean/Lemmas/picard-application/PicardConclusion.lean#L65-L76) · [The twelve hypotheses](#the-twelve-hypotheses)

[**Read the illustrated proof (PDF)**](docs/blueprint/blueprint.pdf) · [**Explore the proof by statement**](docs/blueprint/proof-map.md)

## The mathematical statement

Under the hypotheses below, there exist a nonnegative integer $`k`$ and a polynomial $`P\in\mathbb{Z}[T,X_1,\ldots,X_k]`$ such that

```math
\forall t\in\mathbb{Q},\qquad
 t\in\mathbb{Z}\quad\Longleftrightarrow\quad
 \exists\, (x_1,\ldots,x_k)\in\mathbb{Q}^k,\quad P(t,x_1,\ldots,x_k)=0.
```

This is what it means for the integers to be *Diophantine over the rationals*. It matters for Hilbert’s tenth problem. Such a polynomial would allow an integer variable in any polynomial equation to be represented by rational variables and an additional equation. An algorithm deciding rational solvability could then decide integer solvability, a problem already known to be undecidable. [Background on Hilbert’s tenth problem](https://isa-afp.org/entries/DPRM_Theorem.html)

## How the proof works

1. **Recognize multiplication.** Glazer and collaborators represent integers by points on an elliptic curve. Positive rank supplies points. A uniform bound on rational height rules out false solutions of the multiplication test. With these two ingredients, Theorem 35 constructs the defining polynomial. [Theorem 35 and its proof](docs/blueprint/sections/polynomial.md#s-35)
2. **Obtain the height bound.** A family of genus-two curves records the six values at which the estimate is needed. Theorem 69 supplies one number field for the whole family. Good reduction controls the relevant primes, and a period comparison relates the height of each Jacobian to the height of its parameter. [Common field](docs/blueprint/sections/descent.md#s-69) · [Good reduction](docs/blueprint/sections/reduction.md#s-82) · [Height comparison](docs/blueprint/sections/periods.md#s-95)
3. **Combine the results.** The same bound now works for every rational parameter outside the six specified values. The arithmetic construction includes those values explicitly. Theorem 113 concludes that one polynomial works for every input. [Theorem 113 and its prerequisites](docs/blueprint/sections/global-height.md#s-113)

The illustrated blueprint has seven sections. Its numbered entries comprise 83 proved implications, 15 definitions, the 12 external hypotheses and three clauses spelling out one of them. Each entry links to its Lean source. [Visual guide](docs/blueprint/proof-map.md) · [Complete dependency diagram](docs/blueprint/proof-dependencies.svg) · [Interactive map for download](docs/blueprint/explorer.html?raw=1)

## The twelve hypotheses

Open a group to read the mathematical statements, their exact Lean formulations and the relevant theorems in the literature. The entries identify where several published results must be combined.

<!-- qualitative-hypotheses:begin -->

<details>
<summary><strong>Elliptic curves and rank</strong></summary>

**5. Tian's parity criterion.** For positive squarefree $`d\equiv5\pmod 8`$, put $`E_d:y^2=x^3-d^2x`$ and $`g(a)=\#(2\,\mathrm{Cl}(\mathbb Q(\sqrt{-a})))`$. In an unordered factorization $`d=\prod a_i`$ with $`a_i\gt 1`$, give the factorization weight $`\prod_i g(a_i)`$. Sum the weights separately for residue patterns $`(5,1,\ldots,1)`$ and $`(7,3,1,\ldots,1)`$ modulo $`8`$. If either sum is odd, every arithmetic continuation of $`L(E_d,s)`$ has order at most one at $`s=1`$. Lemma 7 proves that this is equivalent to the normalization in the Lean hypothesis.

[Lean statement](https://github.com/nasqret/z-in-q-lean/blob/95357929cf16cedd3dd1960c11060cb923f5bdca/bounded/PublishedGenusRows.lean#L234-L235) · [Tian, Theorem 4.7 and §4.3](https://intlpress.com/site/pub/files/_fulltext/journals/iccm/2017/0005/0001/ICCM-2017-0005-0001-a003.pdf#page=8)

**6. Rank at a simple central zero.** For a nonsingular elliptic curve $`E/\mathbb Q`$, a simple zero of its arithmetic $`L`$-function at $`s=1`$ implies that $`E(\mathbb Q)`$ contains a point of infinite order. Gross–Zagier give this consequence for modular elliptic curves, and modularity supplies the general case.

[Lean statement](https://github.com/elliotglazer/diophantine-z-q/blob/2358394558aafae202a1ce6d3bd1b536b79ad3d0/ZInQKernel/Hypotheses/CR3Literature.lean#L70-L72) · [Gross–Zagier, I, §7, Theorem 3](https://math.bu.edu/people/svh/GZ1.pdf#page=7) · [Breuil–Conrad–Diamond–Taylor, Theorem A](https://math.stanford.edu/~conrad/papers/tswfinal.pdf#page=1)

</details>

<details>
<summary><strong>Prym varieties and isogeny descent</strong></summary>

**44. Finiteness in degree at most two.** Put $`f_{u,v}(X)=(X^2+2X-2)(4u(2X-1)-vX^3(X+4))`$. For a smooth sextic fibre let $`J_j`$ be the Jacobian of $`y^2=f_{j,1}(x)/2`$. Only finitely many $`j\in\overline{\mathbb Q}`$ with $`[\mathbb Q(j):\mathbb Q]\le2`$ have $`J_j`$ containing an elliptic subvariety. The source proves bounded-degree finiteness for CM points on the marked Prym line. Its application here uses the identification of that line and simplicity up to isogeny.

[Lean statement](https://github.com/nasqret/z-in-q-lean/blob/95357929cf16cedd3dd1960c11060cb923f5bdca/Lean/Lemmas/picard-application/PicardConclusion.lean#L24-L25) · [Laga–Shnidman, Remark 2.12 and Lemmas 6.2, 6.16](https://doi.org/10.1112/jlms.70347)

**48. Endomorphisms of the published Prym sextic.** Let $`L/\mathbb Q`$ be finite Galois, $`a,w\in L`$ and $`\Delta=a^2-4w^3`$, with $`aw\Delta\ne0`$. Suppose $`L`$ contains a primitive cube root of unity and a sixth root of $`16w^3\Delta`$. If the Jacobian $`J`$ of the smooth sextic $`-aw y^2=(x^2+2x-2)(w^3x^4+4w^3x^3+2\Delta x-\Delta)`$ is geometrically simple, then $`\mathrm{End}^0_L(J)=\mathrm{End}^0_{\overline{\mathbb Q}}(J)`$ is the quaternion division algebra generated by $`i^2=-3`$, $`j^2=2`$, $`ji=-ij`$. Here $`\mathrm{End}^0=\mathrm{End}\otimes_{\mathbb Z}\mathbb Q`$. The identification of the two algebras uses the isogeny to the published Prym over $`L`$.

[Lean statement](https://github.com/nasqret/z-in-q-lean/blob/95357929cf16cedd3dd1960c11060cb923f5bdca/Lean/Lemmas/picard-application/PicardPrym.lean#L98-L104) · [Laga–Shnidman, Remark 2.12, Lemma 6.2, Theorem 6.5 and Corollary 6.6](https://doi.org/10.1112/jlms.70347) · [Ritzenthaler–Romagny, Theorem 1.1](https://doi.org/10.46298/epiga.2018.volume2.3663)

**52. Multiplication by a nonzero integer.** For an abelian variety $`A`$ over a field of characteristic zero and any $`n\in\mathbb Z\setminus\{0\}`$, multiplication $`[n]:A\to A`$ is finite, flat and surjective.

[Lean statement](https://github.com/nasqret/z-in-q-lean/blob/95357929cf16cedd3dd1960c11060cb923f5bdca/Lean/Lemmas/picard-application/GuitartSurfaces.lean#L23-L26) · [Milne, Abelian Varieties, Theorem 8.2](https://www.jmilne.org/math/xnotes/AVs.pdf#page=13)

**57. The rational central cocycle.** Let $`Y/L`$ be an abelian surface with the full quaternion algebra just described. If every Galois conjugate admits an $`L`$-isogeny to $`Y`$ intertwining its rational endomorphisms, these isogenies can be chosen so that $`\mu_g\,{}^g\mu_h=c(g,h)\mu_{gh}`$ in rational homomorphisms, where $`c`$ is a $`\mathbb Q^\times`$-valued $`2`$-cocycle on $`\mathrm{Gal}(L/\mathbb Q)`$ and $`c(1,1)=1`$. Guitart's central multiplier must descend to this finite quotient with the indicated composition law.

[Lean statement](https://github.com/nasqret/z-in-q-lean/blob/95357929cf16cedd3dd1960c11060cb923f5bdca/Lean/Lemmas/picard-application/GuitartSurfaces.lean#L60-L66) · [Guitart, Definition 2.1 and p. 594](https://ems.press/content/serial-article-files/38384?nt=1#page=4)

**60. Guitart's descent theorem in the chosen models.** For such a surface obtained by extension of scalars, suppose the multiplier splits over a finite Galois $`M\supseteq L`$ as $`c(g,h)=b(g)b(h)/b(gh)`$ after inflation. Put $`E=\mathbb Q(b(g):g\in\mathrm{Gal}(M/\mathbb Q))`$, $`m=[E:\mathbb Q]`$. There is an abelian variety $`B/\mathbb Q`$ of dimension $`2m`$ and a geometric isogeny $`\kappa:Y_{\overline{\mathbb Q}}^m\to B_{\overline{\mathbb Q}}`$ with $`\mathrm{End}^0_{\mathbb Q}(B)\simeq E\otimes_{\mathbb Q}\mathrm{End}^0_{\overline{\mathbb Q}}(Y)`$. For the coefficient action $`\phi`$, the required restriction law is $`\,{}^\sigma\kappa=\kappa\circ\phi(b(\sigma|_M)^{-1})`$ for $`\sigma\in\mathrm{Gal}(\overline{\mathbb Q}/M)`$. Both conclusions concern the same $`B`$ and $`\kappa`$.

[Lean statement](https://github.com/nasqret/z-in-q-lean/blob/95357929cf16cedd3dd1960c11060cb923f5bdca/Lean/Lemmas/picard-application/GuitartSurfaces.lean#L73-L82) · [Guitart, Proposition 2.10 and Corollary 2.12](https://ems.press/content/serial-article-files/38384?nt=1#page=7)

**62. Tate's splitting theorem for discrete coefficients.** For the discrete coefficient group $`\overline{\mathbb Q}^{\,\times}`$ with **trivial** action, $`H^2_{\mathrm{cont}}(\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q),\overline{\mathbb Q}^{\,\times})=0`$. In particular a cocycle on any finite Galois quotient becomes the coboundary of a locally constant cochain upon inflation. This is the form used by the formalization.

[Lean statement](https://github.com/nasqret/z-in-q-lean/blob/95357929cf16cedd3dd1960c11060cb923f5bdca/Lean/Lemmas/picard-application/GuitartApplication.lean#L104-L107) · [Tate in Ribet, Theorem 6.3](https://math.berkeley.edu/~ribet/Articles/korea.pdf#page=13)

</details>

<details>
<summary><strong>Good reduction</strong></summary>

**77. The split-sextic criterion for good reduction.** Let $`K/\mathbb Q_p`$ be finite unramified with $`p`$ odd, and let $`f\in\mathcal O_K[X]`$ be a separable sextic with six integral roots in $`K`$. If every nonempty cluster strictly below the full root set has odd cardinality, and $`\nu_S`$ is even for every principal cluster $`S`$, then the Jacobian of $`y^2=f(x)`$ has good reduction over $`K`$. A cluster is a nonempty intersection of the roots with a valuation disc. The integer $`\nu_S`$ is the valuation of the leading coefficient plus the sum, over roots $`r`$, of the depths of the smallest clusters containing $`S`$ and $`r`$. The formal statement uses the ring of Witt vectors of the residue field.

[Lean statement](https://github.com/nasqret/z-in-q-lean/blob/95357929cf16cedd3dd1960c11060cb923f5bdca/Lean/Lemmas/picard-application/PicardGoodReduction.lean#L90-L102) · [Dokchitser–Dokchitser–Maistret–Morgan, Theorems 1.9(5) and 10.3(5)](https://doi.org/10.1007/s00208-021-02319-y)

**80. Good reduction under quotient and unramified descent.** For every prime $`p`$ and finite unramified $`K/\mathbb Q_p`$, a surjective homomorphism $`A\to B`$ of abelian varieties over $`K`$ carries good reduction of $`A`$ to good reduction of $`B`$. If $`B/\mathbb Q_p`$ acquires good reduction over $`K`$, it already has good reduction over $`\mathbb Q_p`$. Both implications use the inertia criterion on a rational Tate module.

[Lean statement](https://github.com/nasqret/z-in-q-lean/blob/95357929cf16cedd3dd1960c11060cb923f5bdca/picard/PicardAssembly.lean#L106-L112) · [Serre–Tate, Theorem 1 and Corollaries 2, 4](https://wstein.org/papers/bib/Serre-Tate-Good_Reduction_of_Abelian_Varieties.pdf)

</details>

<details>
<summary><strong>Stable heights and periods</strong></summary>

**90. Compatible heights over every candidate descent field.** Fix a height $`h_F`$ on rational abelian varieties. Over each finite Galois $`M/\mathbb Q`$ there exist **one** height $`F`$ and **one** embedding $`\eta:M\hookrightarrow\mathbb C`$ with the following properties.

- $`F(A^n)=nF(A)`$ for $`n\ge1`$, $`|F(X)-F(Y)|\le\tfrac12\log\deg\varphi`$ for an $`M`$-isogeny $`\varphi:X\to Y`$, and $`F(B_M)=h_F(B)`$ for $`B/\mathbb Q`$.
- There are $`c\gt 0`$ and $`k\in\mathbb N`$ such that if $`Y`$ is $`M`$-isogenous to $`X`$ and $`0\lt \dim X\le2[M:\mathbb Q]`$, there is an $`M`$-isogeny $`X\to Y`$ of degree at most $`c\max(1,F(X))^k`$.
- For each smooth sextic $`y^2=f(x)`$ over $`M`$, there is one genus-two period $`Z`$ with algebraic projective theta coordinates and a common weighted scale $`w\ne0`$ for the identities $`-120Q_2(f)=w h_{12}(Z)/h_{10}(Z)`$ and $`\mathrm{disc}(f)=w^5 h_{10}(Z)`$ after applying $`\eta`$. At that same theta point, of height $`\theta`$, the Jacobian $`J`$ must satisfy $`|\theta-(F(J)+\log\pi)/2|\le96\log(16)\log(\max(1,\theta)+2)`$. The period, the normalization of the height and the Jacobian in all three comparisons must agree.

[Lean statement](https://github.com/nasqret/z-in-q-lean/blob/95357929cf16cedd3dd1960c11060cb923f5bdca/Lean/Lemmas/picard-application/PicardConclusion.lean#L55-L60) · [von Känel, §2.1 and (3.1)](https://doi.org/10.1017/fms.2021.29) · [Gaudron–Rémond, Théorème 1.4](https://lmbp.uca.fr/~gaudron/art13.pdf) · [Streng, Lemma 7.3 and Remark 7.10](https://doi.org/10.1090/S0025-5718-2013-02712-3) · [Milne, Jacobian Varieties, Theorem 12.1](https://www.jmilne.org/math/xnotes/JVs.pdf) · [Pazuki, Definitions 2.1, 2.6 and Corollary 1.3(1)](https://doi.org/10.24033/bsmf.2623)

**100. The effective height bound of von Känel.** Let $`B/\mathbb Q`$ have dimension $`g\gt 0`$, good reduction outside a finite set of primes $`S`$, and a number field of degree $`g`$ embedded in $`\mathrm{End}^0_{\mathbb Q}(B)`$. Put $`N=\prod_{p\in S}p`$, $`r=\#\{p\in S:p\le2g+1\}`$ and $`v=(2g+1)^{6r}N^2`$. With von Känel's normalization the required inequality is $`h_F(B)\le g(18000v^{12}+(8g)^6\log v)`$. Its use on the generic fibre passes through the abelian scheme over $`\mathbb Z[1/N]`$.

[Lean statement](https://github.com/nasqret/z-in-q-lean/blob/95357929cf16cedd3dd1960c11060cb923f5bdca/picard/PicardAssembly.lean#L79-L82) · [von Känel, Theorem 6.2, inequality (6.7)](https://doi.org/10.1017/fms.2021.29)

</details>

<!-- qualitative-hypotheses:end -->

<a id="formalization-dashboard"></a>

## Other constructions and code

Glazer’s quantitative construction requires a specific numerical height estimate. A separate comparison gives 85 total variables for a particular family under further hypotheses. The qualitative theorem above makes neither numerical assertion. [Glazer’s bounded theorem](bounded/README.md) · [Variable bounds](docs/variable-bound.md)

The geometry package contains the final theorem. The root package builds 31 foundational modules with Lean 4.35.0. Two arithmetic lemmas have also passed a separate six-kernel Comparator run. [Build the final theorem](geometry/README.md) · [Comparator results](docs/palomar.md#arithmetic-already-checked)

The project dashboard records the status of the wider development, including alternative constructions. The proof map was organized using Bartosz Naskręcki’s Labyrinth Exploration method. [Project dashboard](dashboard/README.md) · [Labyrinth Exploration](https://github.com/nasqret/labyrinth-exploration)

[Palomar verification status](docs/palomar.md) · [Sources and attribution](docs/sources.md) · [Repository license](LICENSE) · [Standalone LaTeX source](docs/blueprint/blueprint.tex)
