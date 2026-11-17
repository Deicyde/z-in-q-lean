import SixConicInvariant
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! Rational points of the actual normalization above the arithmetic
Igusa chart G_m. The coordinate ring embeds in its own fraction field.
Every finite birational extension of this ring is trivial. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.CMRepair
open BinaryCover ShimuraAtlas
noncomputable section

abbrev OpenRing := LaurentPolynomial ℚ

theorem openRing_normal : IsIntegrallyClosed OpenRing :=
  isIntegrallyClosed_of_isLocalization OpenRing (Submonoid.powers (X : ℚ[X]))
    (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero)

/-- Affine form of the finite-birational normal-target lemma. -/
theorem normalization_bijective {R S K : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] [Module.Finite R S] [Field K] [Algebra R K] [IsFractionRing R K]
    (i : S →ₐ[R] K) (hi : Function.Injective i) : Function.Bijective (algebraMap R S) := by
  constructor
  · intro x y h
    apply IsFractionRing.injective R K
    simpa only [i.commutes] using congrArg i h
  · intro s
    have integral : IsIntegral R (i s) := IsIntegral.map i (Algebra.IsIntegral.isIntegral s)
    obtain ⟨r, hr⟩ := (isIntegrallyClosed_iff K).mp (inferInstance : IsIntegrallyClosed R) integral
    exact ⟨r,hi ((i.commutes r).trans hr)⟩

def rationalUnitEval (q : ℚ) (hq : q ≠ 0) : OpenRing →+* ℚ :=
  LaurentPolynomial.eval₂ (RingHom.id ℚ) (Units.mk0 q hq)

theorem coordinate_at_rational_unit (q : ℚ) (hq : q ≠ 0) :
    rationalUnitEval q hq (LaurentPolynomial.T 1) = q := by
  simp [rationalUnitEval,LaurentPolynomial.eval₂_T]

/-- A rational value of the arithmetic coordinate has a unique rational
lift to each finite birational model on the smooth arithmetic chart. -/
theorem rational_point_of_normalization {S : Type} [CommRing S] [Algebra OpenRing S]
    [Module.Finite OpenRing S] (i : S →ₐ[OpenRing] FractionRing OpenRing) (hi : Function.Injective i)
    (q : ℚ) (hq : q ≠ 0) :
    ∃! l : S →+* ℚ, l.comp (algebraMap OpenRing S) = rationalUnitEval q hq := by
  let := openRing_normal
  let e : OpenRing ≃+* S := RingEquiv.ofBijective (algebraMap OpenRing S) (normalization_bijective i hi)
  let value := rationalUnitEval q hq
  refine ⟨value.comp e.symm.toRingHom, ?_, ?_⟩
  · apply RingHom.ext
    intro r
    change value (e.symm (e r)) = value r
    rw [e.symm_apply_apply]
  · intro m hm
    apply RingHom.ext
    intro s
    obtain ⟨r,rfl⟩ := e.surjective s
    change m (e r) = value (e.symm (e r))
    rw [e.symm_apply_apply]
    exact DFunLike.congr_fun hm r

/-- The lift is a morphism with domain Spec ℚ in the category of schemes over ℚ. -/
theorem rational_scheme_lift {S : Type} [CommRing S] [Algebra ℚ S] [Algebra OpenRing S]
    [Module.Finite OpenRing S] (i : S →ₐ[OpenRing] FractionRing OpenRing) (hi : Function.Injective i)
    (q : ℚ) (hq : q ≠ 0) :
    ∃ p : SpecOver (R := ℚ) ℚ ⟶ SpecOver (R := ℚ) S,
      p ≫ specHom (algebraMap OpenRing S).toRatAlgHom = specHom (rationalUnitEval q hq).toRatAlgHom := by
  obtain ⟨l, hl, _⟩ := rational_point_of_normalization i hi q hq
  refine ⟨specHom l.toRatAlgHom, ?_⟩
  rw [spec_comp]
  congr 1
  exact AlgHom.ext (fun x => DFunLike.congr_fun hl x)

end
end ZInQBlueprint.CMRepair
#print axioms ZInQBlueprint.CMRepair.openRing_normal
#print axioms ZInQBlueprint.CMRepair.normalization_bijective
#print axioms ZInQBlueprint.CMRepair.coordinate_at_rational_unit
#print axioms ZInQBlueprint.CMRepair.rational_point_of_normalization
#print axioms ZInQBlueprint.CMRepair.rational_scheme_lift
