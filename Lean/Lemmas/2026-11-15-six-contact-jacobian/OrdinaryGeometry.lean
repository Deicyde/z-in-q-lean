import OrdinaryForms
import IntegralCoverProper
import IntegralCoverSmooth
import IntegralFibres
import SmoothSextic
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! An integral model for the ordinary six-contact parameters, including its geometric fibres. -/
open Polynomial CategoryTheory AlgebraicGeometry
open ZInQBlueprint.BinaryCover
namespace ZInQBlueprint.OrdinaryModel
noncomputable section
variable {R : Type} [CommRing R] [IsNoetherianRing R]

theorem smooth_proper {s t : R} (hs : IsUnit s) (h2 : IsUnit (2:R)) (ht : IsUnit t)
    (hD : IsUnit (t^2+27)) : Smooth (model s t).hom ∧ IsProper (model s t).hom := by
  let : Invertible (2:R) := h2.invertible
  have sm (i : Bool) :
      Smooth (SpecOver (R := R) (Cover (chartPair s t i))).hom :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr
      (IntegralCover.smooth_cover _ (pair_regular hs h2 ht hD i)))
  exact ⟨smooth_glued _ _ (overlap s t) (sm false) (sm true),
    IntegralCover.glued_proper R _ _ (overlap s t)⟩

variable {s t : R} (hs : IsUnit s) (h2 : IsUnit (2:R)) (ht : IsUnit t)
    (hD : IsUnit (t^2+27))

include hs h2 ht hD in
omit [IsNoetherianRing R] in
theorem field_chart (K : Type) [Field K] (φ : R →+* K) (i : Bool) :
    IsDomain (Cover ((chartPair s t i).map φ)) ∧ IsDedekindDomain (Cover ((chartPair s t i).map φ)) := by
  rw [chart_map]
  have h2' : IsUnit (2:K) := by simpa only [map_ofNat] using h2.map φ
  let : Invertible (2:K) := h2'.invertible
  have hd := pair_degree (hs.map φ).ne_zero h2'.ne_zero (ht.map φ).ne_zero i
  have sep := pair_regular (hs.map φ) h2' (ht.map φ) (by simpa only [map_add,map_pow,map_ofNat] using hD.map φ) i
  exact ⟨domain_separable_cover (by omega) sep,dedekind_cover (by omega) sep⟩

include hs h2 ht hD in
omit [IsNoetherianRing R] in
theorem geom_integral : GeometricallyIntegral (model s t).hom := by
  let : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) AlgebraicGeometry.IsIntegral :=
    ⟨fun e _ => AlgebraicGeometry.IsIntegral.of_isIso e.hom⟩
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := AlgebraicGeometry.IsIntegral) (R := R) (f := (model s t).hom)).mpr
  intro K F φ
  exact IntegralCover.fibre_integral R (chartPair s t) (overlap s t) K
    (fun i => (field_chart hs h2 ht hD K (algebraMap R K) i).1)

end
end ZInQBlueprint.OrdinaryModel
#print axioms ZInQBlueprint.OrdinaryModel.smooth_proper
#print axioms ZInQBlueprint.OrdinaryModel.field_chart
#print axioms ZInQBlueprint.OrdinaryModel.geom_integral
