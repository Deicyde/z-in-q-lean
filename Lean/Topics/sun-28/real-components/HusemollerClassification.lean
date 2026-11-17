import EllipticCircleModel

/-! A curve-level statement of Husemöller, Introduction §7, Proposition 7.2. -/
namespace Sun28.RealComponents
open WeierstrassCurve ZInQ Sun28.Scalar Sun28.RealRatio Sun28.RealCharts
open scoped Sun28.RealCharts
noncomputable section

/-- The three-real-root case of the published theorem, restricted to real curves
in short Weierstrass form and stated in their projective topology. -/
def PublishedProposition72 : Prop := ∀ (a b : ℝ),
    (∃ r s t : ℝ, r≠s ∧ r≠t ∧ s≠t ∧
      ∀ x : ℝ, x^3+a*x+b=(x-r)*(x-s)*(x-t)) →
    Nonempty ((⟨0,0,0,a,b⟩ : WeierstrassCurve ℝ).toAffine.Point ≃ₜ+ Circle × ZMod 2)

/-- Sun's models meet the printed three-real-root hypothesis at both embeddings. -/
theorem models_of_published (published : PublishedProposition72) : HusemollerModels := by
  intro i
  let σ := place i
  let d := σ (3-sqrt2)
  obtain ⟨factor,nz,mnz,neq⟩ := three_real_roots σ
  have roots : ∃ r s t : ℝ, r≠s ∧ r≠t ∧ s≠t ∧
      ∀ x : ℝ, x^3+(-d^2)*x+0=(x-r)*(x-s)*(x-t) := by
    refine ⟨0,d,-d,nz.symm,mnz.symm,neq,fun x => ?_⟩
    have factor_x : x^3-d^2*x=x*(x-d)*(x+d) := factor x
    linear_combination factor_x
  have curve_eq : (curve (-(3-sqrt2)^2)).map σ=(⟨0,0,0,-d^2,0⟩ : WeierstrassCurve ℝ) := by
    ext <;> simp [curve,WeierstrassCurve.map,d]
  change Nonempty (((curve (-(3-sqrt2)^2)).map σ).toAffine.Point ≃ₜ+ Circle × ZMod 2)
  rw [curve_eq]
  exact published (-d^2) 0 roots

/-- The real geometry of the conditional projection now uses the printed
three-root classification alone. -/
theorem openComponent_of_published (published : PublishedProposition72) :
    Sun28.RealProjection.OpenComponent :=
  openComponent_of_husemoller (models_of_published published)

theorem integer_definition_28_of_published (published : PublishedProposition72)
    (units : Sun28.FiveMarkUnits.PublishedCorollary72) (height : Sun28.MinimalConductors.ExactLeastHeight)
    (patterns : Sun28.NormSieve.PrimeValuesWithResidues) (twists : Sun28.PairedClasses.Residual) :
    Sun28.IntegerDefinition28 :=
  integer_definition_28 (models_of_published published) units height patterns twists

end
end Sun28.RealComponents
#print axioms Sun28.RealComponents.models_of_published
#print axioms Sun28.RealComponents.openComponent_of_published
#print axioms Sun28.RealComponents.integer_definition_28_of_published
