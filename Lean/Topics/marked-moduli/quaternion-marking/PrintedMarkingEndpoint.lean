import ThetaDivisorMarking
import AbelConductorEndpoint

/-! Glazer's bounded theorem from a marked polarized isomorphism on the
published model and a normalized period identity on the rational Jacobian. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.JacobianConductor
open GeometricMarking NormalDescent JacobianHeight LocalJacobians AbelianModel QuaternionMarking ZInQ
noncomputable section

theorem original_of_printed_marking (hF : GroupScheme ℚ → ℝ)
    (effective : EffectiveSurfaceHeight hF) (streng : StrengEstimates)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (torelli : ∀ (u : ℚ) (hu : u ∉ contactSet),
      let D := SixAbelMap.divisorData hu
      PolarizedTorelli D (preservesTheta D))
    (bg : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (d : Qbar) (hd : d^2=6)
      (v : Qbar) (hv : v^2=PrintedModel.factor u d),
      PrintedMarking (SixAbelMap.divisorData hu) (PrintedModel.jacobianIso hu hd v hv))
    (periods : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (JacobianPeriods K hF hu))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := by
  apply original_of_marking_and_periods hF effective streng ddmm _ periods genus rank
  intro u hu
  obtain ⟨d,hd,v,hv,hM⟩ := bg u hu
  exact marked_of_theta (SixAbelMap.divisorData hu) (PrintedModel.jacobianIso hu hd v hv)
    (torelli u hu) hM

end
end ZInQBlueprint.JacobianConductor
#print axioms ZInQBlueprint.JacobianConductor.original_of_printed_marking
