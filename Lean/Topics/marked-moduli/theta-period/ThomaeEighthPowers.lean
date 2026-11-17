import AlgebraicThetaPeriod
import Mathlib.RingTheory.Algebraic.Basic

/-! The field-of-definition consequence of the first Thomae formula after
raising to the eighth power. The analytic Thomae identity is an input. -/
namespace ZInQBlueprint.ThetaPeriod
open ThetaQuotient
noncomputable section

/-- The ten even coordinates have a common eighth-power scale times
nonzero algebraic numbers; odd theta-null values vanish. -/
structure EighthPowerData (z : Tuple) where
  value : Fin 10 → ℂ
  algebraic : ∀ i, IsAlgebraic ℚ (value i)
  nonzero : ∀ i, value i ≠ 0
  scale : ℂˣ
  identity : ∀ i, z (evenIndices i)^8 = (scale:ℂ)*value i
  odd_zero : ∀ i, (¬ ∃ k, evenIndices k = i) → z i = 0

theorem eighth_even_nonzero {z : Tuple} (f : EighthPowerData z) : pct z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ h
  have he := f.identity i
  rw [h,zero_pow (by decide)] at he
  exact mul_ne_zero f.scale.ne_zero (f.nonzero i) he.symm

theorem eighth_ratios_algebraic {z : Tuple} (f : EighthPowerData z) :
    ∀ i, IsAlgebraic ℚ (chart z i) := by
  intro j
  by_cases h : ∃ i, evenIndices i = j
  · obtain ⟨i,rfl⟩ := h
    apply IsAlgebraic.of_pow (by decide : 0 < 8)
    rw [chart,div_pow,f.identity i,f.identity 0,
      mul_div_mul_left _ _ f.scale.ne_zero]
    rw [div_eq_mul_inv]
    exact ((f.algebraic i).isIntegral.mul (f.algebraic 0).inv.isIntegral).isAlgebraic
  · rw [chart,f.odd_zero j h,zero_div]
    exact isAlgebraic_zero

/-- Squaring removes the root-of-unity choice in the product of ten fourth powers. -/
theorem eighth_absolute_square {z : Tuple} (f : EighthPowerData z) :
    absInvariant z ^ 2 = (∑ i, f.value i)^10 / (∏ i, f.value i) := by
  have hs : psi z = (f.scale:ℂ)*(∑ i, f.value i) := by
    simp only [psi,f.identity,Finset.mul_sum]
  have hp : pct z ^ 8 = (f.scale:ℂ)^10*(∏ i, f.value i) := by
    simp [pct,← Finset.prod_pow,f.identity,Finset.prod_mul_distrib]
  rw [absInvariant,div_pow,show (psi z ^ 5)^2 = psi z ^ 10 by ring,
    show (pct z ^ 4)^2 = pct z ^ 8 by ring,hp,hs,mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero _ f.scale.ne_zero)

end
end ZInQBlueprint.ThetaPeriod
#print axioms ZInQBlueprint.ThetaPeriod.eighth_even_nonzero
#print axioms ZInQBlueprint.ThetaPeriod.eighth_ratios_algebraic
#print axioms ZInQBlueprint.ThetaPeriod.eighth_absolute_square
