import MarkedConductorEndpoint
import CanonicalJacobianPoints

/-! Glazer's bounded polynomial from the labelled order on the geometric
Jacobian and periods of its canonical principal polarization. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.JacobianConductor
open GeometricMarking NormalDescent JacobianHeight LocalJacobians AbelianModel ZInQ
open scoped NormalDescent
noncomputable section

/-- The point group and the action of each geometric group automorphism are
canonical. The divisor hypotheses are the Abel map, generation by point
differences, and linear equivalence of the fibres of the hyperelliptic map. -/
theorem original_of_divisors_order_and_periods (hF : GroupScheme ℚ → ℝ)
    (effective : EffectiveSurfaceHeight hF) (streng : StrengEstimates)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (marking : ∀ (u : ℚ) (hu : u ∉ contactSet),
      ∃ (D : DivisorData hu) (preserves : (geometricJacobian hu ≅ geometricJacobian hu) → Prop),
        PolarizedTorelli D preserves ∧ ∃ i : realOrder →+* End (geometricJacobian hu),
          Function.Injective i ∧ Labelled i (correction preserves))
    (periods : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (JacobianPeriods K hF hu))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := by
  apply original_of_marking_and_periods hF effective streng ddmm _ periods genus rank
  intro u hu
  obtain ⟨D, preserves, T, i, hi, label⟩ := marking u hu
  exact ⟨markedAction_of_divisors D preserves T i hi label⟩

end
end ZInQBlueprint.JacobianConductor
#print axioms ZInQBlueprint.JacobianConductor.original_of_divisors_order_and_periods
