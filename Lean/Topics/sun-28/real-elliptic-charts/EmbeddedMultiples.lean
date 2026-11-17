import EmbeddedExceptions

/-! Base change of the actual signed orbit to the two real Weierstrass curves. -/
namespace Sun28.RealCharts
open ZInQ WeierstrassCurve WeierstrassCurve.Affine Sun28.Scalar Sun28.RealRatio
noncomputable section

private abbrev W := curve (-(3-sqrt2)^2)

/-- The coordinate embedding of the manuscript's curve as a homomorphism of point groups. -/
def embeddedHom (σ : K0 →+* ℝ) : PaperPoint →+ EmbeddedPoint σ where
  toFun := embedded σ
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁,y₁,h₁⟩) (_ | ⟨x₂,y₂,h₂⟩)
    any_goals simp only [← Point.zero_def,zero_add,add_zero,embedded]
    by_cases pair : x₁=x₂ ∧ y₁=W.negY x₂ y₂
    · have eq₁ := congrArg σ pair.1
      have eq₂ : σ y₁=(W.map σ).negY (σ x₂) (σ y₂) := by rw [pair.2,map_negY]
      rw [Point.add_of_Y_eq pair.1 pair.2]
      change (0 : EmbeddedPoint σ)=_+_
      symm
      exact Point.add_of_Y_eq eq₁ eq₂
    · have lifted : ¬(σ x₁=σ x₂ ∧ σ y₁=(W.map σ).negY (σ x₂) (σ y₂)) := by
        intro h
        exact pair ⟨σ.injective h.1,σ.injective (by simpa only [map_negY] using h.2)⟩
      rw [Point.add_some pair]
      simp only [Point.add_some lifted,map_slope,map_addX,map_addY]

theorem embedded_multiple (σ : K0 →+* ℝ) (m : ℤ) :
    embedded σ (paperMultiple m)=m • embedded σ (paperGenerator sqrt2_sq) :=
  (embeddedHom σ).map_zsmul _ _

end
end Sun28.RealCharts
#print axioms Sun28.RealCharts.embeddedHom
#print axioms Sun28.RealCharts.embedded_multiple
