import SignedAutodualityInjective
import CartierMultiplicity

/-! The degree formula for an effective nondegenerate line bundle in
characteristic zero. The inputs below quantify over every abelian variety
over the algebraic closure. They mention no curve, determinant or marking. -/
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ThetaClass
open QuaternionMarking GeometricMarking AbelianModel NormalDescent CanonicalTheta DeterminantAutoduality
noncomputable section

/-- Milne, Abelian Varieties, Propositions 9.1 and 10.1. An effective line
with finite translation kernel is ample and its translates cover Picard-zero. -/
def EffectivePolarizationImage : Prop :=
  ∀ (A : GroupScheme Qbar) (ab : IsAbelianScheme A) (L : A.X.left.Modules) (hL : L.IsInvertible),
    (∃ s : 𝟙_ A.X.left.Modules ⟶ L, s ≠ 0) → Finite (polarization ab L hL).ker →
      PrincipalTranslations (A:=A) L

/-- In characteristic zero the degree is the number of geometric kernel
points. Theorem 13.3(a,c) and a nonzero section give degree = h⁰ squared. -/
def EffectivePolarizationDegree : Prop :=
  ∀ (A : GroupScheme Qbar) (ab : IsAbelianScheme A) (L : A.X.left.Modules) (hL : L.IsInvertible),
    (∃ s : 𝟙_ A.X.left.Modules ⟶ L, s ≠ 0) → Finite (polarization ab L hL).ker →
      Nat.card (polarization ab L hL).ker = ThetaLinearSystem.rankH0 A.X.hom L ^ 2

theorem one_and_principal_of_injective {A : GroupScheme Qbar} (ab : IsAbelianScheme A)
    (L : A.X.left.Modules) (hL : L.IsInvertible) (s : 𝟙_ A.X.left.Modules ⟶ L) (hs : s ≠ 0)
    (inj : Function.Injective (polarization ab L hL))
    (image : EffectivePolarizationImage) (degree : EffectivePolarizationDegree) :
    ThetaLinearSystem.rankH0 A.X.hom L = 1 ∧ PrincipalTranslations (A:=A) L := by
  let φ := polarization ab L hL
  let : Subsingleton φ.ker := ⟨fun x y => Subtype.ext (inj (x.property.trans y.property.symm))⟩
  let : Finite φ.ker := Finite.of_injective (fun _ => PUnit.unit) (fun _ _ _ => Subsingleton.elim _ _)
  have eq := degree A ab L hL ⟨s,hs⟩ (inferInstanceAs (Finite φ.ker))
  change Nat.card φ.ker = _ at eq
  rw [Nat.card_unique,pow_two] at eq
  exact ⟨Nat.eq_one_of_dvd_one ⟨_,eq⟩,image A ab L hL ⟨s,hs⟩ (inferInstanceAs (Finite φ.ker))⟩

theorem determinant_of_injective {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (inj : Function.Injective (signedPolarization hu))
    (image : EffectivePolarizationImage) (degree : EffectivePolarizationDegree)
    (factor : CartierPrimeFactorization) : DeterminantPolarization hu := by
  have h := one_and_principal_of_injective
    (isAbelianScheme_baseChange (algebraMap ℚ Qbar) (SixJacobian.isAbelian hu))
    _ (signedThetaLine_invertible hu) _ (signedThetaSection_ne_zero hu) inj image degree
  exact ⟨h.1,h.2,rational_of_prime_factorization hu factor (signed_deck_abel_support hu)⟩

/-- The signed determinant satisfies the classical polarization criterion over
the algebraic closure. The three external statements apply to arbitrary
abelian varieties or arbitrary regular noetherian schemes. -/
theorem signed_determinant_of_standard_facts {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (image : EffectivePolarizationImage) (degree : EffectivePolarizationDegree)
    (factor : CartierPrimeFactorization) : DeterminantPolarization hu :=
  determinant_of_injective hu (signedPolarization_injective hu) image degree factor

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.EffectivePolarizationImage
#print axioms ZInQBlueprint.ThetaClass.EffectivePolarizationDegree
#print axioms ZInQBlueprint.ThetaClass.one_and_principal_of_injective
#print axioms ZInQBlueprint.ThetaClass.determinant_of_injective
#print axioms ZInQBlueprint.ThetaClass.signed_determinant_of_standard_facts
