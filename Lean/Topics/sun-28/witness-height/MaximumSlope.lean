import MarkedHeights

/-! The same ordinary detector can be used for both height inequalities. -/
namespace Sun28.WitnessHeight
open Sun28.Ordinary Height
noncomputable section

/-- Select one of the three actual detector slopes of maximal height. -/
theorem maximum_exists (t : Fin 3 → ℚ) :
    ∃ j : Fin 3, ∀ i, logHeight₁ (t i) ≤ logHeight₁ (t j) := by
  obtain ⟨j, _, h⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3))
    (fun i => logHeight₁ (t i)) Finset.univ_nonempty
  exact ⟨j, fun i => h i (Finset.mem_univ i)⟩

/-- The radical at a single maximum divides both discrepancies. The other two
slopes enter only through the height comparison in the choice of the maximum. -/
theorem ordinary_of_maximum (S : Finset ℕ) (t : Fin 3 → ℚ) (n : Fin 4 → ℤ) (β : ℚ)
    {C c₁ c₂ : ℝ} (hC : 1≤C) (hc₁ : 0≤c₁) (hc₂ : 0≤c₂)
    (scale : ∀ H : ℝ, 1≤H → (∀ i, logHeight₁ (t i)≤H) → (indexSize n)^2≤c₁*H+c₂)
    (j : Fin 3) (largest : ∀ i, logHeight₁ (t i)≤logHeight₁ (t j))
    (height : logHeight₁ (t j)≤C*(∏ p∈contactPrimes S (t j),(p:ℝ))^24)
    (divides : (∏ p∈contactPrimes S (t j),(p:ℤ))^64 ∣ lucas (n 1) (n 2) (n 3) ∧
      (∏ p∈contactPrimes S (t j),p)^16 ∣ (β-n 0).num.natAbs) :
    (lucas (n 1) (n 2) (n 3)≠0 → (indexSize n)^2≤ordinaryConstant C c₁ c₂*
      (1+|((lucas (n 1) (n 2) (n 3):ℤ):ℝ)|^(3/8:ℝ))) ∧
    (β≠(n 0:ℚ) → (indexSize n)^2≤ordinaryConstant C c₁ c₂*
      (1+((β-n 0).num.natAbs:ℝ)^(3/2:ℝ))) := by
  apply ordinary_height_bounds S (fun _ => t j) n β hC hc₁ hc₂ (fun _ => height) _ (fun _ => divides)
  exact fun H hH bounded => scale H hH (fun i => (largest i).trans (bounded 0))

end
end Sun28.WitnessHeight

#print axioms Sun28.WitnessHeight.maximum_exists
#print axioms Sun28.WitnessHeight.ordinary_of_maximum
