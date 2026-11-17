import OrdinaryReduction
import OrdinaryFibreDimension
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothSmoothOfRelativeDimension
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothOfRelativeDimensionTopologicalKrullDimPreimageSingletonEq

/-! The integral ordinary sextic is smooth of relative dimension one. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ZInQBlueprint.BinaryCover
namespace ZInQBlueprint.OrdinaryModel
noncomputable section

theorem relative_dimension (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {s t : R} (hs : IsUnit s) (h2 : IsUnit (2:R)) (ht : IsUnit t) (hD : IsUnit (t^2+27)) :
    SmoothOfRelativeDimension 1 (model s t).hom := by
  let M := model s t
  let f := M.hom
  let : Smooth f := (smooth_proper hs h2 ht hD).1
  let : GeometricallyIntegral f := geom_integral hs h2 ht hD
  let : AlgebraicGeometry.IsIntegral M.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian f
  obtain ⟨n,hn⟩ := Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace f
  let : SmoothOfRelativeDimension n f := hn
  let K := FractionRing R
  let ℓ := scalarMap R K
  let g := pullback.snd f ℓ
  let G := pullback f ℓ
  let : SmoothOfRelativeDimension n g := inferInstanceAs (SmoothOfRelativeDimension n (pullback.snd f ℓ))
  let y : Spec (.of K) := Classical.choice (inferInstanceAs (Nonempty (PrimeSpectrum K)))
  have reg := field_chart hs h2 ht hD K (algebraMap R K)
  let : AlgebraicGeometry.IsIntegral G := IntegralCover.fibre_integral R (chartPair s t) (overlap s t) K
    (fun i => (reg i).1)
  have hy : g.base ⁻¹' {y} = Set.univ := Set.eq_univ_iff_forall.mpr fun x =>
    (show g x = y from Subsingleton.elim _ _)
  have H : topologicalKrullDim (g.base ⁻¹' {y}) = n :=
    SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq _ _ y (hy ▸ Set.univ_nonempty)
  rw [hy,IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ G).isHomeomorph] at H
  have hg : topologicalKrullDim G=1 := IntegralCover.fibre_dimension R (chartPair s t) (overlap s t) K
  rw [hg] at H
  have e : n=1 := by exact_mod_cast H.symm
  exact e ▸ hn

end
end ZInQBlueprint.OrdinaryModel
#print axioms ZInQBlueprint.OrdinaryModel.relative_dimension
