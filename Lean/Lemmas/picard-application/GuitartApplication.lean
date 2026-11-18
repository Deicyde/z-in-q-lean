import PicardPolynomial
import GuitartFormula

/-! From the endomorphism algebra and the descent law of Guitart
to the rational quaternionic variety in the polynomial theorem. -/
open CategoryTheory AlgebraicGeometry
open ZInQBlueprint.AbelianModel
open scoped ZInQBlueprint.NormalDescent TensorProduct
open ZOverQ.Qualitative.PicardPolynomial ZOverQ.Qualitative.PicardConjugation
namespace ZOverQ.Qualitative.GuitartApplication
noncomputable section
set_option maxHeartbeats 1600000

/-- Guitart, Corollary 2.12: the displayed tensor product gives the central
coefficient action and the two rational endomorphisms of the descended abelian variety. -/
def quaternionVarietyOfTensor {E D : Type} [Field E] [NumberField E] [Ring D] [Nontrivial D] [Algebra ℚ D]
    (B : GroupScheme ℚ) (hB : IsAbelianScheme B)
    (dim : SmoothOfRelativeDimension (2 * Module.finrank ℚ E) B.X.hom)
    (e : (E ⊗[ℚ] D) ≃ₐ[ℚ] (ℚ ⊗[ℤ] End B))
    (i j : D) (hi : i^2 = -3) (hj : j^2 = 2) (skew : j*i = -(i*j)) : QuaternionVariety E := by
  let A := ℚ ⊗[ℤ] End B
  let T := E ⊗[ℚ] D
  let ι := e.toRingHom.comp (algebraMap E T)
  let alg : Algebra E A := ι.toAlgebra' fun x y => by
    obtain ⟨z,rfl⟩ := e.surjective y
    change e _ * e z = e z * e _
    rw [← map_mul, ← map_mul, Algebra.commutes]
  let tower : IsScalarTower ℚ E A := IsScalarTower.of_algebraMap_eq fun x => by
    change _ = e (algebraMap E T (algebraMap ℚ E x))
    rw [← IsScalarTower.algebraMap_apply, e.commutes]
  let ne : Nontrivial A := e.injective.nontrivial
  let ιD : D →ₐ[ℚ] A := e.toAlgHom.comp Algebra.TensorProduct.includeRight
  exact { B := B, abelian := hB, dimension := dim, nontrivialEnd := ne, centralScalars := alg,
          tower := tower, i := ιD i, j := ιD j,
          sq_i := by rw [← map_pow, hi, map_neg, map_ofNat],
          sq_j := by rw [← map_pow, hj, map_ofNat],
          skew := by rw [← map_mul, skew, map_neg, map_mul] }

open UniformDescent GuitartDescent ZInQ ZInQ.QualitativeHeight

abbrev surface (M : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) (ψ : fixedField →ₐ[ℚ] M)
    (t : ℚ) (ht : t ∉ contactSet) := (baseChange ψ.toRingHom).obj (twistedJacobian t ht)

abbrev sourcePower (M : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) (ψ : fixedField →ₐ[ℚ] M)
    (t : ℚ) (ht : t ∉ contactSet) (b : Gal(M/ℚ) → (AlgebraicClosure ℚ)ˣ) :=
  AbelianPowers.power (surface M ψ t ht) (Module.finrank ℚ (coefficientField b) - 1)

abbrev geometric (M : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :=
  baseChange (algebraMap M (AlgebraicClosure ℚ))

/-- The data from Guitart, Proposition 2.10 and Corollary 2.12, on one
fibre. The endomorphism algebra in the tensor product belongs to its
actual geometric Jacobian. The splitting formula is restricted to
automorphisms fixing M, where the diagonal isogeny is the identity. -/
structure GeometricIsogenyData (M : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (J A : GroupScheme M)
    (b : Gal(M/ℚ) → (AlgebraicClosure ℚ)ˣ) where
  B : GroupScheme ℚ
  abelian : IsAbelianScheme B
  dimension : SmoothOfRelativeDimension (2 * Module.finrank ℚ (coefficientField b)) B.X.hom
  endomorphisms :
    (coefficientField b ⊗[ℚ] (ℚ ⊗[ℤ] End ((geometric M).obj J))) ≃ₐ[ℚ] (ℚ ⊗[ℤ] End B)
  nontrivial : Nontrivial (ℚ ⊗[ℤ] End ((geometric M).obj J))
  i : ℚ ⊗[ℤ] End ((geometric M).obj J)
  j : ℚ ⊗[ℤ] End ((geometric M).obj J)
  sq_i : i^2 = -3
  sq_j : j^2 = 2
  skew : j*i = -(i*j)
  representation : coefficientField b →ₐ[ℚ] (ℚ ⊗[ℤ] End ((geometric M).obj A))
  κ : (geometric M).obj A ⟶
    (geometric M).obj ((baseChange (algebraMap ℚ M)).obj B)
  finite : IsFinite κ.hom.hom.hom.left
  onto : AlgebraicGeometry.Surjective κ.hom.hom.hom.left
  splitting : GeometricLaw M (A:=A) (B:=(baseChange (algebraMap ℚ M)).obj B) b representation κ

/-- Guitart's data attached to the Jacobian and the indicated positive power. -/
abbrev GeometricIsogeny (M : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (ψ : fixedField →ₐ[ℚ] M) (t : ℚ) (ht : t ∉ contactSet)
    (b : Gal(M/ℚ) → (AlgebraicClosure ℚ)ˣ) :=
  GeometricIsogenyData M (surface M ψ t ht) (sourcePower M ψ t ht b) b

/-- Descend the geometric isogeny, and transport its central coefficient
action through the tensor-product identification of the endomorphism ring. -/
theorem marked_fibre (M : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (J A : GroupScheme M) (hA : IsAbelianScheme A)
    (b : Gal(M/ℚ) → (AlgebraicClosure ℚ)ˣ) (c : Gal(M/ℚ) × Gal(M/ℚ) → ℚˣ) (hc : c (1,1) = 1)
    (hb : ∀ g h, rationalUnit (c (g,h)) = b g * b h / b (g*h))
    [NumberField (coefficientField b)]
    (multiply : Multiplications) (W : GeometricIsogenyData M J A b) :
    ∃ V : QuaternionVariety (coefficientField b),
      ∃ f : A ⟶ (baseChange (algebraMap ℚ M)).obj V.B,
        IsFinite f.hom.hom.hom.left ∧ AlgebraicGeometry.Surjective f.hom.hom.hom.left := by
  let := W.nontrivial
  let V := quaternionVarietyOfTensor W.B W.abelian W.dimension W.endomorphisms W.i W.j W.sq_i W.sq_j W.skew
  obtain ⟨f,hf⟩ := descended_isogeny M hA (isAbelianScheme_baseChange (algebraMap ℚ M) W.abelian)
    b c hc hb W.representation W.κ W.finite W.onto multiply W.splitting
  exact ⟨V,f,hf⟩


local instance finiteNumberField (M : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) : NumberField M := ⟨⟩

/-- Tate’s splitting theorem with the discrete multiplicative group of the
algebraic closure under trivial action (Ribet, Theorem 6.3). -/
def TateSplitting (L : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) : Prop :=
  ∀ c : groupCohomology.cocycles₂ (trivialRepresentation Gal(L/ℚ) coefficients),
    ∃ b : LocallyConstant Gal((AlgebraicClosure ℚ)/ℚ) coefficients,
      ∀ σ τ : Gal((AlgebraicClosure ℚ)/ℚ), c (restriction L σ, restriction L τ) = coboundary b σ τ

/-- The normalized cocycle of the endomorphism-compatible conjugate isogenies
over L and the geometric conclusions of Proposition 2.10 and Corollary 2.12
for each of its splitting cochains. -/
def GeometricSystems (L : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (ψ : fixedField →ₐ[ℚ] L) (except : Finset ℚ) : Prop :=
  ∀ (t : ℚ) (ht : t ∉ contactSet), picardParameter t ∉ except →
    ∃ c : Gal(L/ℚ) × Gal(L/ℚ) → ℚˣ, c (1,1) = 1 ∧
      (∀ g h j, c (g*h,j) * c (g,h) = c (h,j) * c (g,h*j)) ∧
      ∀ (M : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) (le : L ≤ M)
        (b : Gal(M/ℚ) → (AlgebraicClosure ℚ)ˣ),
        (∀ g h, rationalUnit (c (finiteRestriction le g, finiteRestriction le h)) = b g * b h / b (g*h)) →
        Nonempty (GeometricIsogeny M ((IntermediateField.inclusion le).comp ψ) t ht b)

set_option maxHeartbeats 1000000 in
/-- The field and dimension bound are selected once, before the variable
parameter. There is no effective splitting-field hypothesis. -/
theorem uniform_marked_isogenies (L : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (ψ : fixedField →ₐ[ℚ] L) (except : Finset ℚ) (tate : TateSplitting L)
    (multiplication : Multiplications) (systems : GeometricSystems L ψ except) :
    ∃ (M : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) (le : L ≤ M),
      MarkedIsogenies ((IntermediateField.inclusion le).comp ψ) (Module.finrank ℚ M) except := by
  obtain ⟨M,le,split⟩ := rational_uniform_splitting_degree L tate
  refine ⟨M,le,?_⟩
  intro t ht away
  obtain ⟨c,normalized,cocycle,geometricData⟩ := systems t ht away
  obtain ⟨b,hb,finite,degree⟩ := split c cocycle
  let : NumberField (coefficientField b) := ⟨⟩
  obtain ⟨W⟩ := geometricData M le b hb
  let ψM := (IntermediateField.inclusion le).comp ψ
  let cM (p : Gal(M/ℚ) × Gal(M/ℚ)) := c (finiteRestriction le p.1,finiteRestriction le p.2)
  have hc : cM (1,1) = 1 := by simpa [cM] using normalized
  have hA : IsAbelianScheme (sourcePower M ψM t ht b) := AbelianPowers.abelian_power
    (isAbelianScheme_baseChange _ (twistedJacobian_abelian t ht)) _
  obtain ⟨V,f,hf⟩ := marked_fibre M (surface M ψM t ht) (sourcePower M ψM t ht b) hA b cM hc hb multiplication W
  exact ⟨coefficientField b, inferInstance, inferInstance, V,degree,f,hf⟩

end
end ZOverQ.Qualitative.GuitartApplication

#print axioms ZOverQ.Qualitative.GuitartApplication.quaternionVarietyOfTensor

#print axioms ZOverQ.Qualitative.GuitartApplication.marked_fibre

#print axioms ZOverQ.Qualitative.GuitartApplication.uniform_marked_isogenies
