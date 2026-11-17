import JacobianConductor
import MarkedTorelli

/-! The original bounded theorem with the explicit list of marking and period inputs. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.JacobianConductor
open GeometricMarking NormalDescent JacobianHeight LocalJacobians AbelianModel ZInQ
open scoped NormalDescent
noncomputable section

/-- The curve-specific stabilizer and rational conductor have proofs upstream
of this statement. Its hypotheses still require geometric divisor coordinates,
a labelled faithful action, and the stable period formula on the signed surface. -/
theorem original_of_labelled_order_and_periods (hF : GroupScheme ℚ → ℝ)
    (effective : EffectiveSurfaceHeight hF) (streng : StrengEstimates)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (comparison : ∀ (u : ℚ) (hu : u ∉ contactSet),
      ∃ (G : Type) (_ : AddCommGroup G) (D : PicardComparison hu G) (polarized : SchemeEnd hu → Prop),
        TorelliOnDifferences D polarized ∧
        ∃ i : realOrder →+* End (geometricJacobian hu), Function.Injective i ∧ Labelled i polarized)
    (periods : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (JacobianPeriods K hF hu))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := by
  apply original_of_marking_and_periods hF effective streng ddmm _ periods genus rank
  intro u hu
  obtain ⟨G, inst, D, polarized, T, i, hi, label⟩ := comparison u hu
  exact ⟨markedAction D polarized T i hi label⟩

end
end ZInQBlueprint.JacobianConductor
#print axioms ZInQBlueprint.JacobianConductor.original_of_labelled_order_and_periods
