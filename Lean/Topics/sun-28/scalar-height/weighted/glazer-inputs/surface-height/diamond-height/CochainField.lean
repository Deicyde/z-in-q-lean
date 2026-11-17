import ScalarCochain
import ScalarFixedField

namespace ZInQBlueprint.DiamondHeight
noncomputable section

/-- (LR3) as a statement about a subfield of the algebraic closure. The global
sign splitting and determinant identity are the inputs on the marked surface. -/
theorem field_of_continuous_splitting {R:ℕ} (L:IntermediateField ℚ Qbar)
    [IsGalois ℚ L] [FiniteDimensional ℚ L] (degree:Module.finrank ℚ L≤576)
    (F : InflatedSplitting (K:=ℂˣ) (AlgEquiv.restrictNormalHom L : GQ →* (L ≃ₐ[ℚ] L)))
    (continuous : Continuous F.b)
    (dy:GQ →* ℂˣ) (dy2:∀ g,(dy g)^2=1)
    (ι : ∀ p:ℕ, GQ →* (ZMod p)ˣ) (χ : ∀ p:ℕ, (ZMod p)ˣ →* ℂˣ)
    (square:∀ g,(F.b g)^2=dy g * ∏ p ∈ R.primeFactors, χ p (ι p g))
    (det:GQ →* ℂˣ) (det2:∀ g ∈ F.restrict.ker.map (markingGroup L).subtype, (det g)^2=1) :
    ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧ IsGalois ℚ E ∧
      E.fixingSubgroup=F.restrict.ker.map (markingGroup L).subtype ∧
      Module.finrank ℚ E≤2304*unitOrders R ∧ det.ker.index≤2*Module.finrank ℚ E := by
  let S:=scalarTower_of_cochain L degree F dy dy2 ι χ square det det2
  have hc : Continuous S.scalar := continuous.comp continuous_subtype_val
  have hopen := continuous_scalar_kernel S (marking_open L) hc
  obtain ⟨E,dim,gal,ker,eqn,bound⟩:=isogeny_field S hopen
  exact ⟨E,dim,gal,ker,bound,eqn ▸ determinant_index S⟩

end
end ZInQBlueprint.DiamondHeight
#print axioms ZInQBlueprint.DiamondHeight.field_of_continuous_splitting
