import PoincareImmersion
import UniversalThetaRestriction
import PrintedMarkingEndpoint
import OpenWeightedAction

/-! Glazer's bounded theorem using the rigidified Poincaré Abel embedding and the coordinate
form of genus-two curve maps on a nonempty open, which may depend on the map. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.JacobianConductor
open GeometricMarking NormalDescent JacobianHeight LocalJacobians AbelianModel QuaternionMarking ZInQ
noncomputable section

theorem original_of_rigid_immersion (hF : GroupScheme ℚ → ℝ)
    (effective : EffectiveSurfaceHeight hF) (streng : StrengEstimates)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (closed : ∀ (u : ℚ) (hu : u ∉ contactSet), IsClosedImmersion (SixAbelMap.rigidMorphism hu).left)
    (coords : ∀ (u : ℚ) (hu : u ∉ contactSet), SixAbelMap.OpenCurveLifts hu)
    (bg : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (d : Qbar) (hd : d^2=6)
      (v : Qbar) (hv : v^2=PrintedModel.factor u d),
      PrintedMarking (SixAbelMap.rigidDivisors hu) (PrintedModel.jacobianIso hu hd v hv))
    (periods : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (JacobianPeriods K hF hu))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := by
  apply original_of_marking_and_periods hF effective streng ddmm _ periods genus rank
  intro u hu
  obtain ⟨d,hd,v,hv,hM⟩ := bg u hu
  let D := SixAbelMap.rigidDivisors hu
  have T : PolarizedTorelli D (preservesTheta D) :=
    SixThetaRestriction.polarizedTorelli_of_presentation hu D (SixAbelMap.rigidMorphism hu)
      (SixAbelMap.rigid_on_points hu) (closed u hu) ((SixAbelMap.curve_lifts_iff_open hu).mpr (coords u hu))
  exact marked_of_theta D (PrintedModel.jacobianIso hu hd v hv) T hM

theorem original_of_rigidified_abel (hF : GroupScheme ℚ → ℝ)
    (effective : EffectiveSurfaceHeight hF) (streng : StrengEstimates)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (milne : ∀ (u : ℚ) (hu : u ∉ contactSet), SixAbelMap.PaperEmbedding hu)
    (coords : ∀ (u : ℚ) (hu : u ∉ contactSet), SixAbelMap.OpenCurveLifts hu)
    (bg : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (d : Qbar) (hd : d^2=6)
      (v : Qbar) (hv : v^2=PrintedModel.factor u d),
      PrintedMarking (SixAbelMap.rigidDivisors hu) (PrintedModel.jacobianIso hu hd v hv))
    (periods : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (JacobianPeriods K hF hu))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := by
  exact original_of_rigid_immersion hF effective streng ddmm
    (fun u hu => SixAbelMap.rigid_closed_of_pointed hu (milne u hu)) coords bg periods genus rank

theorem original_of_unramified_abel (hF : GroupScheme ℚ → ℝ)
    (effective : EffectiveSurfaceHeight hF) (streng : StrengEstimates)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (unramified : ∀ (u : ℚ) (hu : u ∉ contactSet), FormallyUnramified (SixAbelMap.rigidMorphism hu).left)
    (coords : ∀ (u : ℚ) (hu : u ∉ contactSet), SixAbelMap.OpenCurveLifts hu)
    (bg : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (d : Qbar) (hd : d^2=6)
      (v : Qbar) (hv : v^2=PrintedModel.factor u d),
      PrintedMarking (SixAbelMap.rigidDivisors hu) (PrintedModel.jacobianIso hu hd v hv))
    (periods : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (JacobianPeriods K hF hu))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := by
  exact original_of_rigid_immersion hF effective streng ddmm
    (fun u hu => SixAbelMap.rigid_closed_of_unramified hu (unramified u hu)) coords bg periods genus rank

end
end ZInQBlueprint.JacobianConductor
#print axioms ZInQBlueprint.JacobianConductor.original_of_rigidified_abel
#print axioms ZInQBlueprint.JacobianConductor.original_of_rigid_immersion
#print axioms ZInQBlueprint.JacobianConductor.original_of_unramified_abel
