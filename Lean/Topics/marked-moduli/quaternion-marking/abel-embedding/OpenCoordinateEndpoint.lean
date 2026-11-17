import AbelEmbeddingEndpoint
import OpenWeightedAction

/-! Glazer's bounded theorem using the closed Abel embedding and the coordinate
form of genus-two curve maps on a nonempty open, which may depend on the map. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.JacobianConductor
open GeometricMarking NormalDescent JacobianHeight LocalJacobians AbelianModel QuaternionMarking ZInQ
noncomputable section

theorem original_of_open_coordinates (hF : GroupScheme ℚ → ℝ)
    (effective : EffectiveSurfaceHeight hF) (streng : StrengEstimates)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (closed : ∀ (u : ℚ) (hu : u ∉ contactSet),
      IsClosedImmersion (SixThetaRestriction.abelMorphism hu).left)
    (coords : ∀ (u : ℚ) (hu : u ∉ contactSet), SixAbelMap.OpenCurveLifts hu)
    (bg : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (d : Qbar) (hd : d^2=6)
      (v : Qbar) (hv : v^2=PrintedModel.factor u d),
      PrintedMarking (SixAbelMap.divisorData hu) (PrintedModel.jacobianIso hu hd v hv))
    (periods : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (JacobianPeriods K hF hu))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := by
  exact original_of_abel_embedding hF effective streng ddmm closed
    (fun u hu => (SixAbelMap.curve_lifts_iff_open hu).mpr (coords u hu))
    bg periods genus rank

end
end ZInQBlueprint.JacobianConductor
#print axioms ZInQBlueprint.JacobianConductor.original_of_open_coordinates
