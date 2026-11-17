import CofinalSelection

namespace Sun28.PrimeMass
open Finset Filter Sun28.FinitePattern Sun28.ContactFactors Sun28.ContactSieve Sun28.WeightedSelection Sun28.SinglePrime
noncomputable section

/-- A sufficient estimate with only an inverse first power of the cutoff. -/
def InverseCutoffInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4 → ℤ), AdmissibleRoots X c q n →
    ∀ d : ℕ, 0 < d → ∀ B : ℕ, ∃ (K : ℕ) (α : ℝ), B ≤ K ∧ 0 < α ∧
      ∀ m : ℕ, ∃ L ≥ max K m,
        frequentRows (Sun28.RealPoleBounds.fixedScale n) d K L (α/(L:ℝ))

theorem cofinal_rates {K : ℕ} {P : ℕ → ℝ → Prop} {α : ℝ} (ap : 0 < α)
    (find : ∀ m : ℕ, ∃ L ≥ max K m,P L (α/(L:ℝ))) (m : ℕ) (D : ℝ) :
    ∃ (L : ℕ) (δ : ℝ), max K m ≤ L ∧ 0 < δ ∧ D < δ*((L:ℝ)*Real.log L) ∧ P L δ := by
  obtain ⟨r,hr⟩ := exists_nat_gt (Real.exp (D/α))
  obtain ⟨L,big,h⟩ := find (max r m)
  have rl : (r:ℝ) ≤ L := by exact_mod_cast (le_max_left r m).trans ((le_max_right _ _).trans big)
  have expLt := hr.trans_le rl
  have lp : 0 < (L:ℝ) := (Real.exp_pos _).trans expLt
  have logLt := (Real.lt_log_iff_exp_lt lp).mpr expLt
  refine ⟨L,α/(L:ℝ),?_,div_pos ap lp,?_,h⟩
  · exact max_le ((le_max_left _ _).trans big) ((le_max_right _ _).trans ((le_max_right _ _).trans big))
  · rw [show α/(L:ℝ)*((L:ℝ)*Real.log L) = Real.log L * α by field_simp]
    exact (div_lt_iff₀ ap).mp logLt

theorem cofinal_of_inverse (input : InverseCutoffInputs) : CofinalInputs := by
  intro X c q n roots d dp B
  obtain ⟨K,α,bk,ap,find⟩ := input X c q n roots d dp B
  exact ⟨K,bk,cofinal_rates ap find⟩

end
end Sun28.PrimeMass
#print axioms Sun28.PrimeMass.cofinal_rates
#print axioms Sun28.PrimeMass.cofinal_of_inverse
