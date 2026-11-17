import NormalSextic
import GeometricCurve
import Mathlib.RingTheory.Valuation.ValuationRing

/-! Descent through the two open charts of a binary sextic. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Set
namespace ZInQBlueprint.BinaryCover
noncomputable section

private theorem transport {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (h : PreValuationRing A) : PreValuationRing B :=
  Function.Surjective.preValuationRing (R := A) e.toRingHom.toMonoidHom.toMulHom e.surjective

/-- Localizations of a Dedekind domain at all primes, including the zero prime, are valuation rings. -/
theorem affine_dedekind_stalk (R : Type) [CommRing R] [IsDedekindDomain R] (x : PrimeSpectrum R) :
    PreValuationRing ((Spec (.of R)).presheaf.stalk x) := by
  let B := Localization.AtPrime x.asIdeal
  have : ValuationRing B := ValuationRing.iff_local_bezout_domain.mpr ⟨inferInstance,inferInstance⟩
  exact transport (Spec.stalkIso (.of R) x).symm.commRingCatIsoToRingEquiv inferInstance

theorem open_stalk_prevaluation {U X : Scheme} (j : U ⟶ X) [IsOpenImmersion j] (y : U) :
    PreValuationRing (X.presheaf.stalk (j y)) ↔ PreValuationRing (U.presheaf.stalk y) := by
  let e := (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨transport e, transport e.symm⟩

variable (K : Type) [Field K] (P : Bool → K[X]) (h : SexticOverlap K (P false) (P true))

/-- The two inclusions with the coordinate polynomial indexed by the chart. -/
def atlasInclusion (i : Bool) : SpecOver (R := K) (Cover (P i)) ⟶ gluedOver K _ _ h := by
  cases i
  · exact chartInclusion K _ _ h false
  · exact chartInclusion K _ _ h true

instance (i : Bool) : IsOpenImmersion (atlasInclusion K P h i).left := by
  cases i <;> exact chartInclusion_open ..

theorem atlas_cover (x : (gluedOver K _ _ h).left) : ∃ i y, (atlasInclusion K P h i).left y = x := by
  let D := diagram K _ _ h
  obtain ⟨i,y,rfl⟩ := (openCover K _ _ h).exists_eq x
  change ∃ i y, (atlasInclusion K P h i).left y = colimit.ι D _ _
  cases i with
  | none => exact ⟨false,D.map (.init false) y,
      congrArg (fun f : D.obj none ⟶ colimit D => f y) (colimit.w D (.init false))⟩
  | some i => cases i <;> exact ⟨_,y,rfl⟩

/-- Two integral charts glued along the puncture give an integral sextic. -/
theorem integral_glued_of_domains (H : ∀ i, IsDomain (Cover (P i))) :
    AlgebraicGeometry.IsIntegral (gluedOver K _ _ h).left := by
  apply integral_of_two_charts (fun i => (SpecOver (R := K) (Cover (P i))).left) (fun i => (atlasInclusion K P h i).left)
  · intro i
    exact (affine_isIntegral_iff _).mpr (H i)
  · exact atlas_cover K P h
  · let D := diagram K _ _ h
    let w : D.obj none := Classical.choice (inferInstanceAs (Nonempty (Spec (.of (Punctured K (P false))))))
    refine ⟨colimit.ι D none w,?_,?_⟩
    · exact ⟨D.map (.init true) w, congrArg (fun f : D.obj none ⟶ colimit D => f w) (colimit.w D (.init true))⟩
    · exact ⟨D.map (.init false) w, congrArg (fun f : D.obj none ⟶ colimit D => f w) (colimit.w D (.init false))⟩

/-- Every stalk in the model is a localization of one of its two coordinate rings. -/
theorem prevaluation_glued_of_dedekind (H : ∀ i, IsDedekindDomain (Cover (P i))) (x : (gluedOver K _ _ h).left) :
    PreValuationRing ((gluedOver K _ _ h).left.presheaf.stalk x) := by
  obtain ⟨i,y,rfl⟩ := atlas_cover K P h x
  let := H i
  exact (open_stalk_prevaluation (atlasInclusion K P h i).left y).mpr (affine_dedekind_stalk _ y)

end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.affine_dedekind_stalk
#print axioms ZInQBlueprint.BinaryCover.open_stalk_prevaluation
#print axioms ZInQBlueprint.BinaryCover.atlas_cover
#print axioms ZInQBlueprint.BinaryCover.integral_glued_of_domains
#print axioms ZInQBlueprint.BinaryCover.prevaluation_glued_of_dedekind
