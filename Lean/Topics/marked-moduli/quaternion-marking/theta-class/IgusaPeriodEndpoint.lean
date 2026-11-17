import IgusaIdealOrders

/-! The original bounded theorem from the classical local Igusa and global
stable-height formulas on the same signed rational Jacobian. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.ThetaClass
open QuaternionMarking GeometricMarking AbelianModel NormalDescent
open JacobianHeight JacobianConductor LocalJacobians ZInQ NumberField
noncomputable section

theorem original_of_igusa_period (hF : GroupScheme ℚ → ℝ) (effective : EffectiveSurfaceHeight hF)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (embedding : ∀ (u : ℚ) (hu : u ∉ contactSet), SixAbelMap.PaperEmbedding hu)
    (coords : ∀ (u : ℚ) (hu : u ∉ contactSet), SixAbelMap.OpenCurveLifts hu)
    (theta : ∀ (u : ℚ) (hu : u ∉ contactSet), DeterminantPolarization hu)
    (bg : ∀ (u : ℚ) (hu : u ∉ contactSet), PrintedField hu)
    (periods : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (IgusaPeriod K hF hu))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := by
  apply original_of_pole_period hF effective ddmm embedding coords theta bg _ genus rank
  intro u hu
  obtain ⟨K,_,_,⟨data⟩⟩ := periods u hu
  exact ⟨K,inferInstance,inferInstance,pole_period_of_igusa data⟩

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.original_of_igusa_period
