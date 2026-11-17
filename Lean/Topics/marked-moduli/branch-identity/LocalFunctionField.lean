import GeometricCurve
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Birational.Birational

/-! The global curve and the function field of its local DDMM equation. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
namespace ZInQBlueprint.BinaryCover
noncomputable section

/-- Restriction to a nonempty open identifies the stalks at the generic points. -/
def functionFieldOfOpen {U X : Scheme} [IrreducibleSpace U] [IrreducibleSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] : X.functionField ≅ U.functionField :=
  eqToIso (congrArg X.presheaf.stalk (genericPoint_eq_of_isOpenImmersion j).symm) ≪≫
    asIso (j.stalkMap (genericPoint U))

/-- Over the actual local field the DDMM affine chart and the rational model
are birational over that field. Both valuation charts are covered. -/
theorem ddmm_birational {p : ℕ} [Fact p.Prime] {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (v a : ℤ_[p]ˣ) (t : ℤ_[p]) (hc : PrimitiveParameters.Coordinates p u t (v : ℤ_[p]) (a : ℤ_[p])) :
    Scheme.BirationalOver (SpecOver (R := ℚ_[p]) (Cover (GoodReductionCharts.polynomial p u v a t))).hom
      ((Over.pullback (scalarMap ℚ ℚ_[p])).obj (paperModel ℚ u)).hom := by
  obtain ⟨j,hj⟩ := ddmm_open_baseChange hu v a t hc
  let := integral_baseChange ℚ_[p] hu
  let : IsOpenImmersion j.left := hj
  let : Nonempty (SpecOver (R := ℚ_[p]) (Cover (GoodReductionCharts.polynomial p u v a t))).left :=
    inferInstanceAs (Nonempty (PrimeSpectrum (Cover (GoodReductionCharts.polynomial p u v a t))))
  let : AlgebraicGeometry.IsIntegral ((Over.pullback (scalarMap ℚ ℚ_[p])).obj (paperModel ℚ u)).left :=
    integral_baseChange ℚ_[p] hu
  let : IsDominant j.left := ⟨j.left.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _⟩
  exact j.left.birationalOver _ _ j.w

private def affineField (R : CommRingCat) [IsDomain R] :
    (Spec R).functionField ≃+* FractionRing R :=
  (FractionRing.algEquiv R (Spec R).functionField).symm.toRingEquiv

/-- The generic field of the rational curve after base change to Q_p is
the fraction field of the actual DDMM coordinate ring. -/
theorem ddmm_functionField {p : ℕ} [Fact p.Prime] {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (v a : ℤ_[p]ˣ) (t : ℤ_[p]) (hc : PrimitiveParameters.Coordinates p u t (v : ℤ_[p]) (a : ℤ_[p])) :
    let := integral_baseChange ℚ_[p] hu
    Nonempty ((pullback (paperModel ℚ u).hom (scalarMap ℚ ℚ_[p])).functionField ≃+*
      FractionRing (Cover (GoodReductionCharts.polynomial p u v a t))) := by
  let := integral_baseChange ℚ_[p] hu
  let A := Cover (GoodReductionCharts.polynomial p u v a t)
  obtain ⟨j,hj⟩ := ddmm_open_baseChange hu v a t hc
  let k : Spec (.of A) ⟶ pullback (paperModel ℚ u).hom (scalarMap ℚ ℚ_[p]) := j.left
  let : IsOpenImmersion k := hj
  let : Nonempty (Spec (.of A)) := inferInstanceAs (Nonempty (PrimeSpectrum A))
  let : AlgebraicGeometry.IsIntegral (Spec (.of A)) := isIntegral_of_isOpenImmersion k
  let : IsDomain A := (affine_isIntegral_iff (.of A)).mp inferInstance
  let : IsDomain (CommRingCat.of A) := ‹IsDomain A›
  exact ⟨(functionFieldOfOpen k).commRingCatIsoToRingEquiv.trans (affineField (.of A))⟩

end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.functionFieldOfOpen
#print axioms ZInQBlueprint.BinaryCover.ddmm_birational
#print axioms ZInQBlueprint.BinaryCover.ddmm_functionField
