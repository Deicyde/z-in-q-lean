# Finite fibres and the 85-variable bound

Let $P_A$ denote Glazer’s quartic presentation in 222 coordinates, one of which is the input $x$. Leave its coefficient $A$ as a parameter. For $a\in\mathbb Q$ define

$$
S_a=\{x\in\mathbb Q:\text{ the equations at }A=a\text{ have a rational solution over }x\}.
$$

The question in this chapter is how many variables are needed to define the family of sets $S_a$. The manuscript takes $A=149^{2n+1}$ for sufficiently large $n$. The projection comparison below makes sense for every rational $A$ and does not identify which coefficients give $S_A=\mathbb Z$. [Original family](https://github.com/elliotglazer/diophantine-z-q/blob/511529bbe9d635194f0c9d925709e77a5d3afa64/research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex#L104-L112)

## The variable count

**Theorem.** There is an integer polynomial $F(A,x,z_1,\ldots,z_{82},w)$ such that, for all $a,x\in\mathbb Q$, the equation $F(a,x,\mathbf z,w)=0$ has a rational solution in $(\mathbf z,w)$ if and only if $x\in S_a$. A second integer polynomial has the same property for all $a\neq0$ with 64 coordinates $z_i$. The comparison allows the total degree to increase. [Detailed proof and computational certificates](../Lean/Topics/general-width/LiteralFamily222.lean)

| Parameters | Coordinates retained besides the inputs | Additional witness | Total variables |
| --- | ---: | ---: | ---: |
| $A$ and $x$ both vary | 82 | 1 | **85** |
| $A$ fixed, $x$ varies | 82 | 1 | **84** |
| $A\ne0$ and $x$ both vary | 64 | 1 | **67** |
| $A\ne0$ fixed, $x$ varies | 64 | 1 | **66** |

For example, at $a=0$ one may specialize $F$ and obtain the 84-variable equation. The second construction uses division by $a$, so its 66-variable specialization requires $a\neq0$. For a fixed rational $a$, multiplying by a common nonzero denominator restores integer coefficients and preserves the rational zeros.

## Why a single additional witness suffices

**Lemma.** Let $X$ be a finite set of algebraic tuples stable under the absolute Galois group of $\mathbb Q$. Suppose that a rational linear form separates the tuples of $X$. For $P\in X$, the value of the form at $P$ is rational if and only if every coordinate of $P$ is rational.

**Proof.** Let $\ell$ be the form. If $\ell(P)$ is rational, every Galois automorphism $\sigma$ satisfies $\ell(\sigma P)=\sigma(\ell(P))=\ell(P)$. Since both $P$ and $\sigma P$ belong to $X$, separation gives $\sigma P=P$. The coordinates are therefore rational. The converse follows from the rationality of the coefficients of $\ell$.

A sequence of monic equations gives finitely many possible tuples above the retained coordinates. Bounds for their number give a finite list of forms. On each specialized fibre at least one form separates its distinct tuples. The polynomial construction also imposes the remaining equations and excludes the forbidden denominators on each tuple. These requirements keep the coordinates of a witness attached to one solution. [Lean construction for finite fibres](../Lean/Topics/sun-28/compiler/SeparatedCompiler.lean) · [Uniform bound](../Lean/Topics/general-width/RelativeWidth.lean)

## Application to the 222-coordinate system

The first elimination retains 83 coordinates of the initial system, including $x$. Of the 139 other coordinates, 89 are constrained singly and 50 are treated in 25 pairs. The resulting system has 67 linear, 22 quadratic and 50 quartic stages. Equations of degree greater than one can have several solutions. For each pair, the leading binary forms have no common projective zero. The corresponding resultant supplies a monic equation after the indicated normalization. The 196 original equations are then tested on the reconstructed tuple. Counting the parameter $A$ and the additional separating value gives $83+1+1=85$.

Lean proves the projection statements for the two explicitly encoded systems of monic equations. The identification of each encoded system with Glazer’s original coefficient table has a written proof and exact computational checks. Formalizing those two identifications is a separate step. [All parameters in Lean](../Lean/Topics/general-width/LiteralFamily222.lean#L23) · [Nonzero parameters in Lean](../Lean/Topics/general-width/LiteralNonzero222.lean#L23) · [Elimination and verification](../Lean/Topics/general-width/LiteralFamily222.lean)
