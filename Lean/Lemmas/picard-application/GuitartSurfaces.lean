import GuitartApplication
import GuitartCocycle
import PicardIntegralHom
import QuaternionModel

/-! Isogeny descent for geometrically quaternionic abelian surfaces.
The two results from Guitart take arbitrary abelian surfaces; the
multiplication equation uses their actual conjugate homomorphisms.
The finite field that works for every fibre is subsequently chosen by
the uniform splitting theorem, independently of the surface. -/

open CategoryTheory AlgebraicGeometry
open ZInQBlueprint.AbelianModel ZInQBlueprint.NormalDescent
open scoped TensorProduct ZInQBlueprint.NormalDescent
open ZOverQ.Qualitative.PicardConjugation
namespace ZOverQ.Qualitative.GuitartSurfaces
open PicardConjugateEnd GuitartApplication GuitartCocycle PicardPolynomial UniformDescent
open ZInQ ZInQ.QualitativeHeight
noncomputable section

/-- Multiplication by a nonzero integer on an abelian variety, Milne,
Abelian Varieties, Theorem 8.2. -/
def MultiplicationTheorem : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : GroupScheme K), IsAbelianScheme A →
    ∀ z : ℤ, z ≠ 0 → let f := (z • 𝟙 A).hom.hom.hom.left
      IsFinite f ∧ Flat f ∧ AlgebraicGeometry.Surjective f

/-- An actual finite surjective arrow satisfying the endomorphism square
for every conjugate. -/
def CompatibleIsogenies {L : Type} [Field L] [CharZero L] (Y : GroupScheme L) : Prop :=
  ∀ σ : Gal(L/ℚ), ∃ m : pull σ Y ⟶ Y, IsFinite m.hom.hom.hom.left ∧
    AlgebraicGeometry.Surjective m.hom.hom.hom.left ∧ ∀ z : QEnd Y,
      comp (asHom (pull σ Y) (change σ.toRingHom Y z)) (PicardIntegralHom.integral _ _ m) =
        comp (PicardIntegralHom.integral _ _ m) (asHom Y z)

/-- Clearing denominators preserves the endomorphism square. -/
theorem compatible_isogenies {K : Type} [Field K] [CharZero K] (Y : GroupScheme K)
    (ab : IsAbelianScheme Y) (multi : MultiplicationTheorem) (maps : ∃ μ : Maps Y, Compatible Y μ) :
    CompatibleIsogenies Y := by
  obtain ⟨μ,h⟩ := maps
  intro σ
  obtain ⟨⟨ν,l,r⟩,comm⟩ := h σ
  let : IsProper Y.X.hom := ab.proper
  obtain ⟨m,k,_,hf,hs,mul⟩ := PicardIntegralHom.isogeny_of_quasi (μ σ) ν l r inferInstance
    (fun n hn => (multi K _ (isAbelianScheme_baseChange σ.toRingHom ab) n hn).1)
    (fun n hn => (multi K _ ab n hn).2.2)
  refine ⟨m,hf,hs,fun z => ?_⟩
  rw [mul,map_zsmul,map_zsmul]
  exact congrArg (k • ·) (comm z)

/-- The rational maps can be chosen to be represented by actual isogenies. -/
def IntegralMaps {L : Type} [Field L] [CharZero L] {Y : GroupScheme L} (μ : Maps Y) : Prop :=
  ∀ σ, ∃ m : pull σ Y ⟶ Y, IsFinite m.hom.hom.hom.left ∧
    AlgebraicGeometry.Surjective m.hom.hom.hom.left ∧ PicardIntegralHom.integral _ _ m = μ σ

/-- The cocycle attached to compatible isogenies, Guitart, p. 594.
The model, its entire rational endomorphism algebra and every compatible
arrow are defined over L. Hence the displayed multiplication descends to
the finite Galois quotient. The section at the identity is normalized. -/
def RationalMultipliers : Prop :=
  ∀ (L : FiniteGaloisIntermediateField ℚ PicardConjugation.Qbar) (Y : GroupScheme L),
    IsAbelianScheme Y → SmoothOfRelativeDimension 2 Y.X.hom →
    PicardPrym.QuaternionModel Y → CompatibleIsogenies Y →
    ∃ (μ : Maps Y) (c : Gal(L/ℚ) × Gal(L/ℚ) → ℚˣ),
      Compatible Y μ ∧ IntegralMaps μ ∧ Multiplier Y μ c ∧ c (1,1) = 1 ∧
      ∀ g h j, c (g*h,j)*c (g,h) = c (h,j)*c (g,h*j)

/-- Guitart, Proposition 2.10 and Corollary 2.12, for the regular
representation of the splitting field of coefficients. The output is the
geometric isogeny, its restricted conjugation law and the calculation of
the endomorphism algebra over ℚ. The arbitrary ground model X fixes the
canonical identifications of its scalar extensions. -/
def GeometricDescent : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (L : FiniteGaloisIntermediateField ℚ PicardConjugation.Qbar)
    (ψ : k →ₐ[ℚ] L) (X : GroupScheme k), let Y := (baseChange ψ.toRingHom).obj X
    IsAbelianScheme Y → SmoothOfRelativeDimension 2 Y.X.hom → PicardPrym.QuaternionModel Y →
    ∀ (μ : Maps Y) (c : Gal(L/ℚ) × Gal(L/ℚ) → ℚˣ),
      Compatible Y μ → IntegralMaps μ → Multiplier Y μ c → c (1,1) = 1 →
      ∀ (M : FiniteGaloisIntermediateField ℚ PicardConjugation.Qbar) (le : L ≤ M) (b : Gal(M/ℚ) → PicardConjugation.Qbarˣ),
        (∀ g h, rationalUnit (c (finiteRestriction le g, finiteRestriction le h)) = b g * b h / b (g*h)) →
        let Z := (baseChange ((IntermediateField.inclusion le).comp ψ).toRingHom).obj X
        Nonempty (GeometricIsogenyData M Z (AbelianPowers.power Z (Module.finrank ℚ (coefficientField b)-1)) b)

/-- An abelian surface from the Picard equation supplies the full hypothesis
on conjugate isogenies once all its quaternionic endomorphisms are defined
over L. This uses the actual Galois pullback of its group scheme. -/
theorem compatible_maps (L : FiniteGaloisIntermediateField ℚ PicardConjugation.Qbar) (ψ : fixedField →ₐ[ℚ] L)
    (t d : ℚ) (ht : t ∉ contactSet) (hd : d ≠ 0)
    (q : PicardPrym.QuaternionModel (familyOver ψ t d ht hd)) :
    ∃ μ : Maps (familyOver ψ t d ht hd), Compatible _ μ := by
  let := q.division
  let := q.rationalAlgebra
  exact choose_maps _ (family_quasi_isogeny ψ t d ht hd q.presentation q.i q.j
    q.sq_i q.sq_j q.skew q.generates)

set_option maxHeartbeats 1600000 in
/-- The sole family input here is the presentation of the full endomorphism
algebra of the actual surface. The multiplier and geometric descent
arguments are applied to that same surface and the same rational cocycle. -/
theorem systems_of_endomorphisms (multi : MultiplicationTheorem) (multipliers : RationalMultipliers) (descent : GeometricDescent)
    (L : FiniteGaloisIntermediateField ℚ PicardConjugation.Qbar) (ψ : fixedField →ₐ[ℚ] L) (except : Finset ℚ)
    (dim : ∀ (t : ℚ) (ht : t ∉ contactSet), SmoothOfRelativeDimension 2 (surface L ψ t ht).X.hom)
    (ends : ∀ (t : ℚ) (ht : t ∉ contactSet), picardParameter t ∉ except →
      Nonempty (PicardPrym.QuaternionModel (surface L ψ t ht))) : GeometricSystems L ψ except := by
  intro t ht away
  obtain ⟨q⟩ := ends t ht away
  let d : ℚ := (PrimitiveTwist.twist (picardParameter t) : ℤ)
  have hd : d ≠ 0 := by dsimp [d]; exact_mod_cast (PrimitiveTwist.positive _).ne'
  have maps := compatible_maps L ψ t d ht hd q
  have hY := isAbelianScheme_baseChange ψ.toRingHom (twistedJacobian_abelian t ht)
  obtain ⟨μ,c,cm,integral,law,norm,assoc⟩ := multipliers L (surface L ψ t ht) hY (dim t ht) q
    (compatible_isogenies _ hY multi maps)
  exact ⟨c,norm,assoc,descent fixedField L ψ (twistedJacobian t ht) hY (dim t ht) q μ c cm integral law norm⟩


end
end ZOverQ.Qualitative.GuitartSurfaces

#print axioms ZOverQ.Qualitative.GuitartSurfaces.compatible_isogenies
#print axioms ZOverQ.Qualitative.GuitartSurfaces.compatible_maps
#print axioms ZOverQ.Qualitative.GuitartSurfaces.systems_of_endomorphisms
