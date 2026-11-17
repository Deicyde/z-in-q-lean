import AbelOrbitGeometry
import DivisorConductorEndpoint

/-! The original bounded polynomial after discharging the complete divisor
comparison on the geometric fibre of the signed rational Jacobian. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.JacobianConductor
open GeometricMarking NormalDescent JacobianHeight LocalJacobians AbelianModel ZInQ
open scoped NormalDescent
noncomputable section

/-- All divisor classes in this statement are the ones from the constructed
Abel morphism of the signed curve. -/
theorem original_of_canonical_divisors (hF : GroupScheme ℚ → ℝ)
    (effective : EffectiveSurfaceHeight hF) (streng : StrengEstimates)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (marking : ∀ (u : ℚ) (hu : u ∉ contactSet),
      ∃ preserves : (geometricJacobian hu ≅ geometricJacobian hu) → Prop,
        PolarizedTorelli (SixAbelMap.divisorData hu) preserves ∧
          ∃ i : realOrder →+* End (geometricJacobian hu),
            Function.Injective i ∧ Labelled i (correction preserves))
    (periods : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (JacobianPeriods K hF hu))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := by
  apply original_of_divisors_order_and_periods hF effective streng ddmm _ periods genus rank
  intro u hu
  exact ⟨SixAbelMap.divisorData hu, marking u hu⟩

end
end ZInQBlueprint.JacobianConductor
#print axioms ZInQBlueprint.JacobianConductor.original_of_canonical_divisors
