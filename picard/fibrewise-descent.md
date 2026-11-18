# A uniform field for the Picard Jacobians

For a rational parameter $`s=X/Y`$ in lowest terms, put $`\rho^2=-3`$, $`u=X+\rho Y`$, $`v=X-\rho Y`$, $`U=u^6`$, and $`V=v^6`$. Let $`J_s`$ be the Jacobian of the smooth genus-two curve

```math
2y^2=f_{U,V}(x),\qquad f_{U,V}(x)=(x^2+2x-2)\bigl(4U(2x-1)-Vx^3(x+4)\bigr).
```

Let $`A_s=J_s^{(e_s)}`$ be the rational quadratic twist used in the local reduction argument. Write $`O_s`$ for the product of the rational primes $`p\gt 3`$ where the primitive branch form has odd valuation. Excluding a further fixed set of primes changes the eventual height bound by a constant factor. [Primitive twist](PrimitiveTwist.lean) · [Local root and cluster calculations](LocalSupport.lean)

**Proposition.** There is a number field $`M`$ of degree $`64`$ over $`\mathbb Q`$, unramified outside $`\{2,3\}`$, with the following property. For all but finitely many smooth rational parameters, there is a rational abelian variety $`B_s`$ of $`\mathrm{GL}_2`$-type and an integer $`1\le m_s\le8`$ such that

```math
(B_s)_M\sim_M (A_s)_M^{m_s},\qquad \dim B_s=2m_s.
```

For smooth rational parameters there are constants independent of the parameter such that

```math
h_F(J_s)\le C_1 O_s^{24},\qquad h(s)\le C_2 O_s^{24}.
```

Here $`h(s)`$ is the absolute logarithmic height. The field and dimension bound are explicit. The height constants use finiteness of the CM parameters and a comparison of heights on the moduli space. The local calculation verifies the published criterion on the integral sextic. Section 4 uses the resulting abelian model after a common unramified extension. The proposition states the written argument. The final section identifies the applications still open in Lean. [Dokchitser–Dokchitser–Maistret–Morgan, Theorem 1.9(5)](https://doi.org/10.1007/s00208-021-02319-y)

## 1. The quaternion algebra and its field of definition

Take $`k=\mathbb Q(\rho)`$ and $`L=\mathbb Q(i,\sqrt2,\sqrt3)=\mathbb Q(\zeta_{24})`$. Put $`\Delta=U-V`$, $`a=2\Delta^2`$, and $`b=-\Delta^3V=(-\Delta v^2)^3`$. For the associated bielliptic Picard curve, Laga and Shnidman's Remark 2.12 gives a $`k`$-isogeny class containing both its Prym and $`J_s`$. Their endomorphism and moduli parameters satisfy

```math
16b(a^2-4b)=(2i\Delta uv)^6,\qquad j=U/V.
```

At a non-CM parameter, Lemma 6.2, Theorem 6.5 and Corollary 6.6 of their paper identify the full geometric rational endomorphism algebra with the division quaternion algebra $`D/\mathbb Q`$ of discriminant six. The endomorphisms are defined over $`L`$. The same application works directly for a nonzero twist $`d`$. Set $`\lambda=v^2/d`$ and replace $`(a,w)`$ by $`(\lambda^3a,\lambda^2w)`$, where $`b=w^3`$. The normalized polynomial in Remark 2.12 becomes $`f_{U,V}/(2d)`$. Its marked invariant remains $`U/V`$, and its endomorphism parameter has sixth root $`\lambda^2(2i\Delta uv)`$ in the same field. [Twisted equation and endomorphisms](../Lean/Lemmas/picard-application/PicardPrym.lean) · [Magma identity](PrymTwist.m)

Thus $`\mathrm{End}^0_L(A_s)=\mathrm{End}^0_{\overline{\mathbb Q}}(A_s)=D`$. By Lemma 6.16 only finitely many CM $`j`$-values have degree at most two. Here $`j\in k`$ and $`s\mapsto j`$ has degree six, so there are only finitely many rational CM parameters. [Laga–Shnidman, §§2.3, 6.1, 6.4](https://doi.org/10.1112/jlms.70347) · [Parameter identities](PrymFactor.lean)

Fix a non-CM fibre $`A=A_s`$. An element of $`G=\mathrm{Gal}(L/\mathbb Q)`$ either fixes $`U,V`$ or interchanges them. In the second case $`x\mapsto-2/x`$, $`y\mapsto2\sqrt{-2}\,y/x^3`$ gives an isomorphism between the conjugate smooth projective curves over $`L`$, including after the rational twist. This follows from $`x^6f_{U,V}(-2/x)=-8f_{V,U}(x)`$. For each $`g\in G`$, the induced group isomorphism $`\,{}^gA\to A`$ acts on $`D`$ by a $`\mathbb Q`$-algebra automorphism. Skolem–Noether makes this automorphism inner. Composing with the inverse implementing quasi-endomorphism gives an $`L`$-quasi-isogeny $`\mu_g`$ with $`\mu_g\,{}^g x=x\,\mu_g`$ for every $`x\in D`$. Take $`\mu_1=1`$. Then

```math
c(g,h)=\mu_g\,{}^g\mu_h\,\mu_{gh}^{-1}\in Z(D)^\times=\mathbb Q^\times
```

is a normalized cocycle for the trivial action. [Conjugate Jacobians](../Lean/Lemmas/picard-application/PicardDescent.lean) · [Wu, §1](https://doi.org/10.4310/MRL.2020.v27.n3.a14) · [Guitart, Definition 2.1](https://ems.press/content/serial-article-files/38384#page=3)

## 2. A common splitting field for the cocycles

For the qualitative theorem one can choose the field by a finiteness argument. For the fixed quotient $`G`$, there are finitely many classes in $`H^2(G,\overline{\mathbb Q}^{\times})`$ with trivial coefficient action. Tate's vanishing theorem makes each inflated class a coboundary on the absolute Galois group. The finitely many splitting maps are locally constant and factor through one finite Galois extension $`M/\mathbb Q`$ containing $`L`$. Changing the cocycle within its class only multiplies the splitting map by a function on $`G`$. Thus this one $`M`$ works for every fibre. In §§3–4 one can use $`[M:\mathbb Q]`$ as the bound on the multiplicity and include the finite set of primes ramifying in $`M`$ in the constant. The qualitative bound uses only the existence of this finite field and the resulting uniform dimension bound. [Uniform field in Lean](UniformDescent.lean) · [Ribet, Theorem 6.3](https://math.berkeley.edu/~ribet/Articles/korea.pdf#page=13)

### An explicit choice giving dimension at most sixteen

Let $`M`$ be the compositum of the splitting fields over $`\mathbb Q`$ of

```math
T^4-2,\qquad T^4-3,\qquad T^4-2T^2+3.
```

Write $`a_0=\sqrt[4]2`$, $`b_0=\sqrt[4]3`$ and $`c_0=\sqrt{1+i\sqrt2}`$. The roots of the first two polynomials are the multiples of $`a_0,b_0`$ by fourth roots of unity. The roots of the third are $`\pm c_0,\ \pm\sqrt3/c_0`$. Hence $`M=L(a_0,b_0,c_0)`$. The polynomial discriminants are $`-2048,-6912,3072`$, so $`M`$ is unramified outside $`\{2,3\}`$. Its degree over $`L`$ is at most eight.

**Lemma.** If $`c`$ is a normalized $`\mathbb Q^\times`$-valued cocycle on $`G`$, its inflation to $`H=\mathrm{Gal}(M/\mathbb Q)`$ is a coboundary with coefficients in $`\overline{\mathbb Q}^{\times}`$ with trivial action.

*Proof.* For a cocycle on the abelian group $`G`$, the commutator $`\lambda(g,h)=c(g,h)/c(h,g)`$ is an alternating bicharacter. Indeed it is the commutator of lifts in the central extension defined by $`c`$. Since $`G`$ has exponent two, its values are signs. In the ordered basis given by the independent sign changes of $`i,\sqrt2,\sqrt3`$, such a form is determined by its values on the pairs $`(1,2),(1,3),(2,3)`$.

Each quartic gives a dihedral extension of order eight over $`\mathbb Q`$, a central double cover of the corresponding biquadratic field. For $`T^4-d`$, $`d=2,3`$, rotation multiplies $`\sqrt[4]d`$ by $`i`$ and reflection fixes the real root and conjugates $`i`$. The biquadratic quotient has characters $`\chi_{-1},\chi_d`$, and its commutator pairing is $`\chi_{-1}\wedge\chi_d`$. For the third quartic put $`t=i\sqrt2`$, $`v=\sqrt3`$, and $`c_0^2=1+t`$. The two independent sign changes on $`\mathbb Q(t,v)`$ lift by

```math
(t,v,c_0)\longmapsto(-t,v,v/c_0),\qquad (t,v,c_0)\longmapsto(t,-v,c_0).
```

The norm of $`1+t`$ from $`\mathbb Q(t)`$ is $`3`$. It is neither a square nor $`3`$ times a square in $`\mathbb Q(t)`$, since the corresponding rational norms would force $`3`$ or $`1/3`$ to be a rational square. An element of $`\mathbb Q(t)`$ becoming a square after adjoining $`v`$ has one of those two forms. Thus $`c_0`$ generates a quadratic extension of $`\mathbb Q(t,v)`$. The two lifts are involutions whose commutator changes $`c_0`$ to $`-c_0`$, giving the third form $`\chi_{-2}\wedge\chi_3`$.

Pull the three central extensions back to $`G`$ and let $`c_1,c_2,c_3`$ be the sign cocycles obtained by choosing sections. Their commutators span all alternating forms on $`G`$, since $`\chi_{-2}=\chi_{-1}+\chi_2`$. The restriction homomorphism from $`H`$ onto each dihedral group lifts the corresponding map from $`H`$ to the biquadratic quotient. The inflated central extension thus has a section over $`H`$, so each inflated $`c_j`$ is a coboundary.

Divide $`c`$ by a product of the $`c_j`$ to have trivial commutator. With coefficients extended to $`\overline{\mathbb Q}^\times`$, the resulting central extension is abelian. Choose commuting lifts of the three generators. Rescaling each by a square root of the inverse of its square gives commuting lifts of order dividing two. These supply a section on $`G`$ itself. This proves the lemma.

The three independent commutator pairings give three independent sign changes on $`(a_0,b_0,c_0)`$ over $`L`$, by taking commutators of lifts in $`H`$. Therefore $`[M:L]=8`$ and $`[M:\mathbb Q]=64`$. An exact Magma computation also tests all seven products of the three radicands for nonsquareness over $`L`$, constructs the degree-64 field and its twelve listed roots, and evaluates the commutators on field elements. The three rows of exponents are $`(1,0,0)`$, $`(0,1,1)`$, and $`(0,0,1)`$. [Magma source](FibrewiseDescent.m)

## 3. Constructing the rational factor

Inflate the isogenies $`\mu_g`$ to the absolute Galois group through $`G`$. They may be chosen to be actual isogenies by clearing the finitely many denominators, keeping $`\mu_1=1`$. Use the cocycle of this choice in §2. Choose a splitting map $`\beta`$ that factors through $`H=\mathrm{Gal}(M/\mathbb Q)`$, so $`c(g,h)=\beta(g)\beta(h)/\beta(gh)`$ after inflation. Let $`E=\mathbb Q(\beta(h):h\in H)`$ and $`m=[E:\mathbb Q]`$. The rational span of the $`\beta(h)`$ contains one and is closed under multiplication. Being a finite-dimensional domain, it is a field. Hence it equals $`E`$ and $`1\le m\le |H|`$. [Coefficient field](UniformDescent.lean)

For the explicit field in §2 we have $`m\le8`$. Put $`N=\mathrm{Gal}(M/L)`$. Normalization gives $`\beta(1)=1`$ and $`\beta(hn)=\beta(h)\beta(n)`$ for $`n\in N`$. Since $`N`$ has exponent two, $`\beta(n)=\pm1`$. One lift of each of the eight elements of $`G`$ therefore spans the coefficient field. [Degree bound](FibrewiseProjector.lean#L146)

**Descent of the isogeny.** Apply Guitart's Proposition 2.10 to the simple abelian $`\mathbb Q`$-variety $`A_{\overline{\mathbb Q}}`$ of §1. Its geometric endomorphism algebra has centre $`\mathbb Q`$. Take the regular representation $`\phi:E\hookrightarrow M_m(\mathbb Q)`$. The proposition gives an abelian variety $`B/\mathbb Q`$ and an isogeny $`\kappa:A^m\to B`$ over $`\overline{\mathbb Q}`$ satisfying

```math
\kappa^{-1}\,{}^\sigma\kappa
   =\phi(\beta(\sigma))^{-1}\widehat\mu_\sigma .
```

Here $`\widehat\mu_\sigma`$ acts by $`\mu_\sigma`$ on each factor. If $`\sigma`$ fixes $`M`$, its image in $`H`$ and in $`G`$ is the identity. Both factors on the right are the identity. Thus $`\kappa`$ is fixed by $`\mathrm{Gal}(\overline{\mathbb Q}/M)`$. Descent of morphisms gives an isogeny over $`M`$, since both its source and target are defined over $`M`$. An equality in rational Hom suffices here: Hom between abelian varieties in characteristic zero is torsion-free. In particular $`\dim B=2m`$. [Descent of the finite surjective morphism in Lean](GuitartDescent.lean#L276) · [Guitart, Proposition 2.10, p. 596](https://ems.press/content/serial-article-files/38384#page=6)

**The field action.** Guitart’s Corollary 2.12 identifies the rational endomorphism algebra of $`B`$ with $`E\otimes_{\mathbb Q}D`$. Use the quaternion generators $`i^2=-3`$, $`j^2=2`$, $`ji=-ij`$. If $`-3`$ is a nonsquare in $`E`$, then $`i`$ generates a quadratic field. Otherwise take $`r^2=-3`$ in $`E`$. The square of $`bj+cij`$ equals $`2(b+rc)(b-rc)`$. For any $`d\in E`$, set $`b+rc=1`$ and $`b-rc=d/2`$. This gives an element with square $`d`$. Some $`d`$ is a nonsquare, since otherwise $`E`$ would contain primitive roots of unity of order $`2^n`$ for every $`n`$. The resulting field acts on $`B`$ and has rational degree $`2m=\dim B`$. The cohomological choice of $`M`$ gives $`\dim B\le2[M:\mathbb Q]`$. [Field action over an arbitrary number field](../Lean/Lemmas/picard-application/GeneralQuaternionField.lean) · [Guitart, Corollary 2.12, p. 598](https://ems.press/content/serial-article-files/38384#page=8) · [von Känel, definition preceding Theorem A](https://doi.org/10.1017/fms.2021.29)

For the explicit dimension bound there is also a direct choice of a quadratic field. In Laga and Shnidman's presentation $`D=(-3,2)`$ take generators $`i,j`$ with $`ij=-ji`$. The four elements $`i,j,ij,i+2j`$ have squares $`-3,2,6,5`$, respectively. Their rational squareclasses are independent, as one sees by taking signs and valuations at $`2,3,5`$. Their four square roots generate a field of degree sixteen. Since $`[E:\mathbb Q]\le8`$, at least one of the four numbers $`d`$ remains a nonsquare in $`E`$. Its indicated quaternion element gives a unital embedding of the field $`E[T]/(T^2-d)`$ in $`E\otimes D`$. [Laga and Shnidman, §4.1](https://doi.org/10.1112/jlms.70347) · [Lean proof for every coefficient field of degree at most eight](QuaternionField.lean) · [Quaternion calculation](FibrewiseDescent.m)

## 4. The exponent in the height bound

Fix a prime $`p\nmid 6O_s`$. The primitive twist and the split-sextic criterion give a finite unramified field $`K/\mathbb Q_p`$ and an abelian model of the base change of $`A_s`$ to $`K`$. The construction specifies an embedding of $`\mathbb Q(\sqrt{-2},\sqrt{-3})`$ in $`K`$ compatible with its chosen sextic. Extend this embedding to an embedding $`M\hookrightarrow\overline{\mathbb Q}_p`$ and let $`M_w`$ be the corresponding completion. Both $`K`$ and $`M_w`$ are finite unramified over $`\mathbb Q_p`$, so their compositum $`K'`$ is finite unramified. Base change the abelian model to its ring of integers. Over $`K'`$, the isogeny of §3 is a surjection from $`A_s^{m_s}`$ to $`B_s`$. Corollary 2 of Serre and Tate’s Theorem 1 gives good reduction of the quotient over $`K'`$. Corollary 4 then gives good reduction of $`B_s`$ over $`\mathbb Q_p`$. Thus von Känel's Theorem A over $`\mathbb Q`$ applies with $`g=\dim B_s\le16`$ and rational bad-prime product dividing $`6O_s`$. It gives

```math
h_F(B_s)\le(3g)^{144g}(6O_s)^{24}.
```

[Serre–Tate, Theorem 1, Corollaries 2 and 4, pp. 493–494](https://annals.math.princeton.edu/1968/88-3/p05) · [von Känel, Theorem A](https://doi.org/10.1017/fms.2021.29)

Use $`(B_s)_M`$ as the reference variety in the isogeny theorem of Gaudron–Rémond. Both the ground-field degree and the dimension are bounded independently of the parameter. In the explicit construction the bounds are $`64`$ and $`16`$. Their theorem supplies a degree polynomial in $`\max(1,h_F(B_s))`$ for an $`M`$-isogeny to $`(A_s)_M^{m_s}`$. The Faltings height variation is at most half the logarithm of this degree. For stable heights this follows after passage to a field of semistable reduction for the two varieties, since degree is preserved by base change. This is von Känel’s equation (3.1) after semistable base change. There are consequently nonnegative constants $`b_1,b_2`$ independent of $`s`$ with

```math
m_s h_F(A_s)\le h_F(B_s)+b_1+b_2\log\max(1,h_F(B_s)).
```

Stable height is additive and invariant under geometric twisting. Since $`m_s\ge1`$, the rational estimate gives $`h_F(J_s)\le C_1O_s^{24}`$. Enlarging $`C_1`$ covers the finite CM set, since $`O_s\ge1`$. [Gaudron–Rémond, Théorème 1.4](https://lmbp.uca.fr/~gaudron/art13.pdf) · [von Känel, equation (3.1) and §5.2.2](https://doi.org/10.1017/fms.2021.29)

## 5. Passing from the Jacobian to the rational parameter

For a smooth binary sextic $`f`$, the degree-zero expression $`R=Q_2(f)^5/\mathrm{disc}(f)`$ is a regular function on the genus-two moduli space in characteristic zero. Here $`Q_2`$ is the normalized quadratic invariant in the ordinary coefficient convention. The conversion is $`I_2=-120Q_2`$, $`I_{10}=\mathrm{disc}(f)`$, so $`R`$ is a fixed rational multiple of $`I_2^5/I_{10}`$. The denominator is nonzero throughout the smooth locus. For this family the calculated expression is

```math
R=\frac{(U^2+25UV+V^2)^5}{9112500\,U^2V^2(U-V)^6}.
```

It is nonconstant, with a pole at $`U=V\ne0`$. For the coordinate used here, the rational calculation gives $`h(s)\le h(R)+450+\log 1024+\log 5+\log 120+\log 3`$ when $`s\ne5`$ and the branch form is nonzero. It uses the degree-twelve estimate in the original coordinate $`t=120/(s-5)`$. The single missing value can be included directly. [Streng, §2.1](https://pub.math.leidenuniv.nl/~strengtc/icp.pdf) · [Discriminant of the actual polynomial](PicardDiscriminant.lean) · [Rational parameter height](../bounded/PicardCriterion.lean)

Via the Torelli morphism the genus-two moduli space is the open part of the moduli space of principally polarized abelian surfaces parametrizing indecomposable polarized surfaces. Thus $`R`$ pulls back to a regular function on the inverse image $`V`$ of that open part at any fixed level. Choose the orthogonal level $`l=16=4^2`$ in Dill's algebraic projective embedding. Every principally polarized geometric Jacobian admits such a level structure. [Cléry–Faber–van der Geer, §§1, 3](https://doi.org/10.1007/s00208-016-1510-2) · [Dill, Proposition 2.1 and §8.1.1](https://doi.org/10.4171/JEMS/1057)

A regular function on a locally closed subvariety of projective space is locally a quotient of homogeneous polynomials of the same degree with nonvanishing denominator. Choose finitely many such charts on $`V`$ by quasi-compactness. If $`z`$ belongs to a chart on which $`R=F/G`$, the local polynomial height inequalities and the product formula give

```math
h(R(z))=h([F(z):G(z)])\le (\deg F)h_{\mathrm{proj}}(z)+C_{F,G}.
```

The level variety, the invariant and these finitely many polynomials are defined over a number field. A level lift can have a larger field of definition, varying with the fibre. The local estimates sum with the normalized local degrees defining the absolute height. Their constants are preserved by finite extension of the field. Taking the maximum over this finite cover therefore bounds the height of the invariant on every geometric level lift.

For this projective embedding, Dill's equation (4.2) gives $`h_{\mathrm{proj}}(z)\le c\max(1,h_F(J_s))`$. Its deduction uses Pazuki's Corollary 1.3(1), a fixed algebraic coordinate change, and equivalence of the two archimedean norms. The separate isogeny-orbit assumption in Dill's Lemma 4.1 enters its equation (4.1). Combining these inequalities gives $`h(s)\le C_2O_s^{24}`$. The comparison uses the algebraic invariant at the canonical polarized Jacobian. This removes the choice of a period matrix for each fibre from the qualitative height proof. [Dill, proof of Lemma 4.1, equation (4.2)](https://ems.press/content/serial-article-files/32563#page=17) · [Pazuki, Corollary 1.3(1)](https://doi.org/10.24033/bsmf.2623)

The fixed-number-field formulation in Lean can be used on the coarse points. Fix a quasi-projective embedding of the coarse genus-two moduli space over $`k`$. The curve and its polarized Jacobian give a coarse point over $`k`$ for each fibre. The regular invariant $`R`$ on that locus is represented on a finite cover by homogeneous pairs over $`k`$. To compare this coarse projective height with Dill's level height, compose the forgetful morphism on $`V`$ with the coarse embedding. On finitely many charts this morphism is given by tuples of homogeneous polynomials of the same degree with no common zero on the chart. The same product-formula estimate for the tuples gives $`h_{\mathrm{coarse}}\le D h_{\mathrm{proj}}+O(1)`$ over every field of definition of a level lift. This verifies the height comparison required on the fixed-field coarse points at the level of the written proof. The specific coarse embedding, its charts and the forgetful morphism still have to be identified with the inputs to the Lean theorem. [Fixed-field chart theorem](PicardAssembly.lean#L269) · [Composition with the Diophantine definition](PicardAssembly.lean#L296)

## The conditional existence theorem

For the analytic comparison, the formal argument applies the published invariant and height formulas at one period of a smooth sextic. The algebraic representative of the theta coordinates may be defined over a number field depending on the fibre. On the rational invariant line the point is $`[R:1]`$. Its normalized projective height is exactly $`h(R)`$. This gives $`h(R)\le84\max(1,h_F(J))+289200`$ with empty exceptional set at this step. [Precise period hypothesis and deduction](../Lean/Lemmas/picard-application/PicardPeriods.lean) · [Streng, Lemma 7.3](https://arxiv.org/pdf/0903.4766#page=18) · [Pazuki, Corollary 1.3 and Definition 2.6](https://doi.org/10.24033/bsmf.2623)

For the descent argument Lean identifies the twisted equation, excludes the finite set of CM parameters, and constructs compatible finite surjective maps for the Galois conjugates. It applies Guitart’s general multiplier law and descent formula to the same surface and cocycle. From Tate’s theorem it chooses one field for all the fibres. The proof then transfers good reduction and stable height along the descended isogeny and applies the qualitative polynomial theorem. The general statements about Pryms, descent, periods, reduction, heights and rank are explicit parameters of the formal implication. [Actual conjugate isogenies](../Lean/Lemmas/picard-application/PicardConjugateEnd.lean) · [Guitart’s hypotheses](../Lean/Lemmas/picard-application/GuitartSurfaces.lean) · [Final theorem](../Lean/Lemmas/picard-application/PicardConclusion.lean)
