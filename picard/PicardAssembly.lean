import LocalSupport
import ThetaComparison
import AbelianModel
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.RingTheory.TensorProduct.Basic

/-! # From abelian varieties of GL₂-type to the integer polynomial

The bad primes are prescribed by the primitive branch form. The height in the
period comparison is the height of the very same rational group scheme to which
the effective Shafarevich theorem is applied. The remaining geometric
hypotheses are explicit in `Fibre` and `integer_polynomial_of_abelian_factors`.
-/
namespace ZOverQ.Qualitative.Picard.Assembly
open ZInQ ZInQ.QualitativeHeight ZInQBlueprint.AbelianModel
open CategoryTheory AlgebraicGeometry
open ZOverQ.Qualitative PicardLocal PrimitiveTwist LocalSupport
open scoped TensorProduct CategoryTheory.MonObj CategoryTheory.Obj
noncomputable section

/-- The rational primes inverted at a fibre. -/
def inverted (fixed : Finset ℕ) (s : ℚ) : Finset ℕ :=
  fixed ∪ (branchInteger s).natAbs.primeFactors.filter fun p => Odd (padicValRat p (primitiveBranch s))

theorem support {fixed : Finset ℕ} (h : ∀ p ∈ fixed, p.Prime) (s : ℚ) :
    ∀ p ∈ inverted fixed s, p.Prime ∧ (p ∈ fixed ∨ Odd (padicValRat p (primitiveBranch s))) := by
  intro p hp
  rcases Finset.mem_union.mp hp with z | z
  · exact ⟨h p z,Or.inl z⟩
  · exact ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp z).1,Or.inr (Finset.mem_filter.mp z).2⟩

theorem mem_inverted {fixed : Finset ℕ} {p : ℕ} [Fact p.Prime] {s : ℚ} :
    p ∈ inverted fixed s ↔ p ∈ fixed ∨ Odd (padicValRat p (primitiveBranch s)) := by
  simp only [inverted,Finset.mem_union,Finset.mem_filter]
  refine or_congr_right ⟨And.right,fun h => ⟨?_,h⟩⟩
  rw [← Nat.support_factorization, Finsupp.mem_support_iff]
  have eqn : padicValRat p (primitiveBranch s) = ((branchInteger s).natAbs.factorization p : ℤ) := by
    rw [← cast_branch,padicValRat.of_int,padicValInt,← Nat.factorization_def _ Fact.out]
  intro h0
  simp [eqn,h0] at h

/-- The local arithmetic supplied to the reduction argument, with the actual
quadratic twist in its defining polynomial and a finite unramified splitting. -/
def ClusterCondition (p : ℕ) [Fact p.Prime] (s : ℚ) : Prop :=
  ∃ (ρ : WittRing p), ρ^2 = -3 ∧ ∃ (A : Finset (Fin 2)) (m : ℕ),
    Nonempty (FibreData p s.num s.den (twist s) ρ A m)

theorem clusters_outside {fixed : Finset ℕ} (h₂ : 2 ∈ fixed) (h₃ : 3 ∈ fixed)
    {s : ℚ} (hb : primitiveBranch s ≠ 0) (p : ℕ) [hp : Fact p.Prime]
    (out : p ∉ inverted fixed s) : 3 < p ∧ p ∉ fixed ∧ ClusterCondition p s := by
  have omitp := not_or.mp (fun h => out (mem_inverted.mpr h))
  have gt : 3 < p := by
    by_contra! h
    have hmin := hp.out.two_le
    interval_cases p <;> simp_all
  obtain ⟨ρ,hr⟩ := exists_rho p gt
  obtain ⟨ρ',hρ,A,m,data⟩ := rational_fibre_data p gt s hb omitp.2 hr
  refine ⟨gt,omitp.1,ρ',?_,A,m,data⟩
  rcases hρ with rfl|rfl <;> simpa using hr

/-- Pointwise addition on commutative group-scheme morphisms. -/
private instance : Preadditive (GroupScheme ℚ) where
  homGroup P Q := ((InducedCategory.homEquiv : (P ⟶ Q) ≃ (P.toGrp ⟶ Q.toGrp)).trans
    Additive.ofMul).addCommGroup
  add_comp _ _ _ f g h := InducedCategory.hom_ext (MonObj.mul_comp f.hom g.hom h.hom)
  comp_add _ _ _ f g h := InducedCategory.hom_ext (MonObj.comp_mul f.hom g.hom h.hom)

/-- A number field of degree g acts on the *rational* endomorphisms over ℚ. -/
def HasGL2Type (B : GroupScheme ℚ) (g : ℕ) : Prop :=
  ∃ (E : Type) (_ : Field E) (_ : NumberField E), Module.finrank ℚ E = g ∧
    Nonempty (E →ₐ[ℚ] (ℚ ⊗[ℤ] End B))

def GoodOutside (B : GroupScheme ℚ) (S : Finset ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ∉ S → GoodReductionAt p B

/-- The GL₂-type case of von Känel, Theorem 6.2 (6.7), stated on the generic
fibre using extension of abelian varieties with good reduction over ℤ[1/N].
The argument hF denotes the stable Faltings height in the paper's convention. -/
def VonKanel (hF : GroupScheme ℚ → ℝ) : Prop :=
  ∀ (B : GroupScheme ℚ) (g : ℕ) (S : Finset ℕ), 0 < g → (∀ p ∈ S, p.Prime) →
    IsAbelianScheme B → SmoothOfRelativeDimension g B.X.hom → HasGL2Type B g → GoodOutside B S →
    hF B ≤ vonKanelBound g S

/-- The outstanding geometric construction for a single parameter. The
reduction implication includes passing from the sextic to its Jacobian and
transferring good reduction to the descended rational factor. -/
structure RationalFactor (g : ℕ) (fixed : Finset ℕ) (s : ℚ) where
  B : GroupScheme ℚ
  abelian : IsAbelianScheme B
  dimension : SmoothOfRelativeDimension g B.X.hom
  fieldAction : HasGL2Type B g
  reduction : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p ∉ fixed → ClusterCondition p s → GoodReductionAt p B

section LocalTransfer
variable (p : ℕ) [Fact p.Prime]

/-- Good reduction over a finite unramified extension, using its own Witt
ring of integers and a group-scheme isomorphism on the generic fibre. -/
def GoodWitt (k : Subfield (Residues p)) (A : GroupScheme (FractionRing (WittVector p k))) : Prop :=
  ∃ M : GroupScheme (WittVector p k), IsAbelianScheme M ∧
    Nonempty ((baseChange (algebraMap (WittVector p k) (FractionRing (WittVector p k)))).obj M ≅ A)

/-- Serre–Tate, Theorem 1, Corollaries 2 and 4, restricted to finite
unramified extensions of ℚ_p. The ring and its ramification index are
identified in LocalSupport.witt_fraction_unramified. -/
def SerreTateAt : Prop := ∀ (k : Subfield (Residues p)) [Finite k],
  letI := wittFractionAlgebra p k
  let K := FractionRing (WittVector p k)
  (∀ (A B : GroupScheme K), IsAbelianScheme A → IsAbelianScheme B →
    ∀ f : A ⟶ B, Surjective f.hom.hom.hom.left → GoodWitt p k A → GoodWitt p k B) ∧
  (∀ B : GroupScheme ℚ_[p], IsAbelianScheme B →
    GoodWitt p k ((baseChange (algebraMap ℚ_[p] K)).obj B) → HasGoodReduction p B)

/-- An actual surjection to the scalar extension of the rational factor from
an abelian variety with a smooth proper group model over the unramified ring. -/
def UnramifiedQuotient (B : GroupScheme ℚ) : Prop :=
  ∃ (k : Subfield (Residues p)) (_ : Finite k),
    letI := wittFractionAlgebra p k
    let K := FractionRing (WittVector p k)
    let Bp := (baseChange (algebraMap ℚ ℚ_[p])).obj B
    ∃ (A : GroupScheme K) (f : A ⟶ (baseChange (algebraMap ℚ_[p] K)).obj Bp),
      IsAbelianScheme A ∧ GoodWitt p k A ∧ Surjective f.hom.hom.hom.left

theorem reduction_of_unramified_quotient (st : SerreTateAt p) {B : GroupScheme ℚ}
    (hB : IsAbelianScheme B) (quotient : UnramifiedQuotient p B) : GoodReductionAt p B := by
  obtain ⟨k,fin,A,f,hA,model,onto⟩ := quotient
  let := wittFractionAlgebra p k
  have bp := isAbelianScheme_baseChange (algebraMap ℚ ℚ_[p]) hB
  have bk := isAbelianScheme_baseChange (algebraMap ℚ_[p] (FractionRing (WittVector p k))) bp
  exact (st k).2 _ bp ((st k).1 _ _ hA bk f onto model)

end LocalTransfer

/-- It suffices to construct local quotient maps after finite unramified
extension; Serre and Tate supply good reduction over the original ℚ_p. -/
def rationalFactorOfQuotients {s : ℚ} {g : ℕ} {fixed : Finset ℕ} (B : GroupScheme ℚ)
    (abelian : IsAbelianScheme B) (dimension : SmoothOfRelativeDimension g B.X.hom)
    (action : HasGL2Type B g) (st : ∀ (p : ℕ) [Fact p.Prime], 3 < p → SerreTateAt p)
    (maps : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p ∉ fixed → ClusterCondition p s → UnramifiedQuotient p B) :
    RationalFactor g fixed s where
  B := B
  abelian := abelian
  dimension := dimension
  fieldAction := action
  reduction := fun p _ gt away data =>
    reduction_of_unramified_quotient p (st p gt) abelian (maps p gt away data)

/-- A rational factor together with its theta and isogeny comparison data. -/
structure Fibre (hF : GroupScheme ℚ → ℝ) (g D : ℕ) (fixed : Finset ℕ) (s : ℚ)
    extends RationalFactor g fixed s where
  periods : Theta.FibreAt s (hF B) D

theorem good_outside {g fixed s} (b : RationalFactor g fixed s)
    (h₂ : 2 ∈ fixed) (h₃ : 3 ∈ fixed) (hb : primitiveBranch s ≠ 0) : GoodOutside b.B (inverted fixed s) := by
  intro p hp out
  obtain ⟨gt,away,localData⟩ := clusters_outside h₂ h₃ hb p out
  exact b.reduction p gt away localData

/-- The endpoint assumes the construction of the rational abelian factors,
the published height theorem, and the two published rank inputs. The odd
prime support and the comparison between numerical heights are deductions. -/
theorem integer_polynomial_of_abelian_factors (hF : GroupScheme ℚ → ℝ) (vk : VonKanel hF)
    (g D : ℕ) (hg : 0 < g) (hD : 0 < D) (fixed : Finset ℕ) (except : Finset ℚ)
    (primes : ∀ p ∈ fixed, p.Prime) (h₂ : 2 ∈ fixed) (h₃ : 3 ∈ fixed)
    (fibres : ∀ s : ℚ, s ∉ except → primitiveBranch s ≠ 0 → Nonempty (Fibre hF g D fixed s))
    (tian : ZInQBlueprint.OriginalRank.PublishedGenusRows.PublishedTian47)
    (grossZagier : ZOverQ.Bounded.SimpleZeroRank) : IntegerPolynomial := by
  classical
  let good (s : ℚ) := s ∉ except ∧ primitiveBranch s ≠ 0
  let fibre (s : ℚ) (h : good s) := (fibres s h.1 h.2).some
  let H (s : ℚ) := if h : good s then hF (fibre s h).B else 0
  apply Theta.integer_polynomial_of_periods g D hD fixed except (inverted fixed) H primes
  · exact fun s _ _ => support primes s
  · intro s hs hb
    have h : good s := ⟨hs,hb⟩
    let b := fibre s h
    simpa only [H,dite_eq_left h,b] using vk b.B g (inverted fixed s) hg
      (fun p hp => (support primes s p hp).1) b.abelian b.dimension b.fieldAction (good_outside b.toRationalFactor h₂ h₃ hb)
  · intro s hs hb
    have h : good s := ⟨hs,hb⟩
    simpa only [H,dite_eq_left h] using (fibre s h).periods
  · exact tian
  · exact grossZagier

/-- In a fixed number field the isogeny estimates of Gaudron and Rémond
bound a minimal isogeny degree by a polynomial in the source height. Passing
to its logarithm preserves the exponent 24 in the bound at the bad primes. -/
theorem comparison_of_polynomial_degree {s : ℚ} {H c : ℝ} {D k : ℕ}
    (hb : primitiveBranch s ≠ 0) (hD : 0 < D) (hc : 0 < c)
    (degree : (D:ℝ) ≤ c*(max 1 H)^k) (periods : Theta.FibreAt s H D) :
    ratHeight (igusaRatio (chart s)) ≤
      (84+42*(k:ℝ))*max 1 H + (42*Real.log c+289200) := by
  have pos : 0 < max 1 H := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have logD := Real.log_le_log (by exact_mod_cast hD : 0 < (D:ℝ)) degree
  rw [Real.log_mul hc.ne' (pow_ne_zero _ pos.ne'),Real.log_pow] at logD
  have logH := Real.log_le_sub_one_of_pos pos
  have := mul_le_mul_of_nonneg_left logH (Nat.cast_nonneg k (α:=ℝ))
  nlinarith only [this,logD,Nat.cast_nonneg (α:=ℝ) k,Theta.comparison_of_fibre hb hD periods]

/-- An affine comparison of the invariant height with the height of a rational
factor suffices, uniformly over all dimensions at most G. -/
theorem integer_polynomial_of_factor_comparison (hF : GroupScheme ℚ → ℝ) (vk : VonKanel hF)
    (G : ℕ) (a b₀ : ℝ) (ha : 0 ≤ a) (fixed : Finset ℕ) (except : Finset ℚ)
    (primes : ∀ p ∈ fixed, p.Prime) (h₂ : 2 ∈ fixed) (h₃ : 3 ∈ fixed)
    (fibres : ∀ s : ℚ, s ∉ except → primitiveBranch s ≠ 0 →
      ∃ (g : ℕ) (b : RationalFactor g fixed s), 0 < g ∧ g ≤ G ∧
        ratHeight (igusaRatio (chart s)) ≤ a*max 1 (hF b.B)+b₀)
    (tian : ZInQBlueprint.OriginalRank.PublishedGenusRows.PublishedTian47)
    (grossZagier : ZOverQ.Bounded.SimpleZeroRank) : IntegerPolynomial := by
  let M := ∑ j ∈ Finset.range (G+1), dimensionCoefficient j
  have dimPos (g : ℕ) : 0 ≤ dimensionCoefficient g := by unfold dimensionCoefficient; positivity
  have mpos : 0 ≤ M := Finset.sum_nonneg fun g _ => dimPos g
  let B : ℝ := b₀ + (450 + Real.log 1024 + ratHeight 5 + ratHeight 120 + ratHeight 0 + Real.log 3)
  obtain ⟨m,_,bound⟩ := exists_uniform_height_bound fixed (insert (5:ℚ) except) (inverted fixed)
    (A:=a*M) (B:=a+B) (mul_nonneg ha mpos) primes (fun s _ _ => support primes s) (by
      intro s hs hb
      have h5 : s ≠ 5 := fun h => hs (Finset.mem_insert.mpr (Or.inl h))
      obtain ⟨g,b,hg,cap,cmp⟩ := fibres s (fun h => hs (Finset.mem_insert_of_mem h)) hb
      let N := ∏ p ∈ inverted fixed s, p
      have ng : dimensionCoefficient g ≤ M := Finset.single_le_sum (f:=dimensionCoefficient)
        (fun j _ => dimPos j) (Finset.mem_range.mpr (by omega : g<G+1))
      have upper : hF b.B ≤ M*(N:ℝ)^24 := calc
        _ ≤ vonKanelBound g (inverted fixed s) := vk b.B g _ hg (fun p hp => (support primes s p hp).1)
          b.abelian b.dimension b.fieldAction (good_outside b h₂ h₃ hb)
        _ ≤ dimensionCoefficient g * (N:ℝ)^24 := vonKanelBound_le _ _ (fun p hp => (support primes s p hp).1)
        _ ≤ M*(N:ℝ)^24 := mul_le_mul_of_nonneg_right ng (by positivity)
      have nonneg : 0 ≤ M*(N:ℝ)^24 := mul_nonneg mpos (by positivity)
      have one : max 1 (hF b.B) ≤ 1+M*(N:ℝ)^24 := max_le (by linarith) (by linarith)
      have transfer := mul_le_mul_of_nonneg_left one ha
      have param := parameter_le_invariant h5 hb
      change ratHeight s ≤ a*M*(N:ℝ)^24 + (a+B)
      dsimp only [B]
      linarith only [transfer,cmp,param])
  exact integer_polynomial_of_uniform_height (C:=(m:ℝ)) bound tian grossZagier

/-- Fibrewise descent suffices. The rational factors may have different
bounded dimensions, and the isogeny degrees may grow polynomially in their
stable heights, with common coefficients. -/
theorem integer_polynomial_of_fibrewise_factors (hF : GroupScheme ℚ → ℝ) (vk : VonKanel hF)
    (G k : ℕ) (c : ℝ) (hc : 0 < c) (fixed : Finset ℕ) (except : Finset ℚ)
    (primes : ∀ p ∈ fixed, p.Prime) (h₂ : 2 ∈ fixed) (h₃ : 3 ∈ fixed)
    (fibres : ∀ s : ℚ, s ∉ except → primitiveBranch s ≠ 0 →
      ∃ (g D : ℕ) (b : Fibre hF g D fixed s), 0 < g ∧ g ≤ G ∧ 0 < D ∧ (D:ℝ) ≤ c*(max 1 (hF b.B))^k)
    (tian : ZInQBlueprint.OriginalRank.PublishedGenusRows.PublishedTian47)
    (grossZagier : ZOverQ.Bounded.SimpleZeroRank) : IntegerPolynomial := by
  apply integer_polynomial_of_factor_comparison hF vk G (84+42*(k:ℝ)) (42*Real.log c+289200)
    (by positivity) fixed except primes h₂ h₃ _ tian grossZagier
  intro s hs hb
  obtain ⟨g,D,b,hg,hG,hD,deg⟩ := fibres s hs hb
  exact ⟨g,b.toRationalFactor,hg,hG,comparison_of_polynomial_degree hb hD hc deg b.periods⟩

section AlgebraicCharts
open ZInQBlueprint.ThetaQuotient Height
variable {K : Type} [Field K] [NumberField K] {n m : ℕ}

/-- On finitely many projective charts of a variety over one number field,
a rational invariant is given by homogeneous pairs of equal degree. -/
structure InvariantCharts (K : Type) [Field K] (n m : ℕ) where
  degree : Fin m → ℕ
  equation : Fin m → Fin 2 → MvPolynomial (Fin n) K
  homogeneous : ∀ i j, (equation i j).IsHomogeneous (degree i)

def InvariantCharts.Represents (P : InvariantCharts K n m) (z : Fin n → K) (r : ℚ) : Prop :=
  ∃ i, (P.equation i 1).eval z ≠ 0 ∧
    (r:K) = (P.equation i 0).eval z / (P.equation i 1).eval z

/-- The degree and coefficient heights of the finitely many pairs give one
linear inequality for the ordinary height of every rational invariant value. -/
theorem height_of_algebraic_charts (P : InvariantCharts K n m) :
    ∃ a b : ℝ, 0 ≤ a ∧ ∀ (z : Fin n → K) (r : ℚ), P.Represents z r →
      ratHeight r ≤ a * normalizedHeight z + b := by
  let d : ℝ := Module.finrank ℚ K
  have hd : 0 < d := by dsimp [d]; exact_mod_cast Module.finrank_pos (R:=ℚ) (M:=K)
  let H (i : Fin m) : ℝ := Real.log (max (Height.mulHeightBound (P.equation i)) 1)
  let N : ℝ := ∑ i, (P.degree i : ℝ)
  let C : ℝ := ∑ i, max 0 (H i)
  refine ⟨N,C/d,Finset.sum_nonneg (fun i _ => Nat.cast_nonneg (P.degree i)),?_⟩
  intro z r ⟨i,_,eqn⟩
  have he := Height.logHeight_eval_le (P.homogeneous i) z
  have pair : (fun j => (P.equation i j).eval z) = ![(P.equation i 0).eval z,(P.equation i 1).eval z] := by
    funext j; fin_cases j <;> rfl
  rw [pair,← Height.logHeight₁_div_eq_logHeight,← eqn, relative_rational_height] at he
  have hi : H i ≤ C := (le_max_right 0 _).trans (Finset.single_le_sum (f:=fun j => max 0 (H j))
    (fun j _ => le_max_left _ _) (Finset.mem_univ i))
  have hN : (P.degree i:ℝ) ≤ N := Finset.single_le_sum (f:=fun j => (P.degree j:ℝ))
    (fun j _ => Nat.cast_nonneg _) (Finset.mem_univ i)
  have hmul := mul_le_mul_of_nonneg_right hN (Height.logHeight_nonneg z)
  change d*ratHeight r ≤ H i + ↑(P.degree i)*Height.logHeight z at he
  change ratHeight r ≤ N*(Height.logHeight z/d)+C/d
  rw [← mul_div_assoc,← add_div,le_div_iff₀ hd]
  linarith only [he,hi,hmul]

/-- A coarse moduli point over a fixed number field is enough. In this form
the geometric inputs are a regular expression for the invariant on the moduli
charts and a linear comparison for the projective height. -/
theorem integer_polynomial_of_moduli_charts (P : InvariantCharts K n m)
    (hF : GroupScheme ℚ → ℝ) (vk : VonKanel hF) (G : ℕ) (u v : ℝ) (hu : 0 ≤ u)
    (fixed : Finset ℕ) (except : Finset ℚ) (primes : ∀ p ∈ fixed, p.Prime)
    (h₂ : 2 ∈ fixed) (h₃ : 3 ∈ fixed)
    (fibres : ∀ s : ℚ, s ∉ except → primitiveBranch s ≠ 0 →
      ∃ (g : ℕ) (b : RationalFactor g fixed s) (z : Fin n → K),
        0 < g ∧ g ≤ G ∧ P.Represents z (igusaRatio (chart s)) ∧ normalizedHeight z ≤ u*max 1 (hF b.B)+v)
    (tian : ZInQBlueprint.OriginalRank.PublishedGenusRows.PublishedTian47)
    (grossZagier : ZOverQ.Bounded.SimpleZeroRank) : IntegerPolynomial := by
  obtain ⟨a,c,ha,estimate⟩ := height_of_algebraic_charts P
  apply integer_polynomial_of_factor_comparison hF vk G (a*u) (a*v+c) (mul_nonneg ha hu)
    fixed except primes h₂ h₃ _ tian grossZagier
  intro s hs hb
  obtain ⟨g,b,z,hg,hG,form,height⟩ := fibres s hs hb
  refine ⟨g,b,hg,hG,?_⟩
  linarith only [estimate z _ form,mul_le_mul_of_nonneg_left height ha]

end AlgebraicCharts

end
end ZOverQ.Qualitative.Picard.Assembly

#print axioms ZOverQ.Qualitative.Picard.Assembly.mem_inverted
#print axioms ZOverQ.Qualitative.Picard.Assembly.clusters_outside
#print axioms ZOverQ.Qualitative.Picard.Assembly.good_outside
#print axioms ZOverQ.Qualitative.Picard.Assembly.integer_polynomial_of_abelian_factors

#print axioms ZOverQ.Qualitative.Picard.Assembly.comparison_of_polynomial_degree
#print axioms ZOverQ.Qualitative.Picard.Assembly.integer_polynomial_of_fibrewise_factors

#print axioms ZOverQ.Qualitative.Picard.Assembly.height_of_algebraic_charts
#print axioms ZOverQ.Qualitative.Picard.Assembly.integer_polynomial_of_moduli_charts

#print axioms ZOverQ.Qualitative.Picard.Assembly.reduction_of_unramified_quotient
#print axioms ZOverQ.Qualitative.Picard.Assembly.rationalFactorOfQuotients
