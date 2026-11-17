import BoundaryStrips
import Mathlib.NumberTheory.Chebyshev

namespace Sun28.ArtinCube
open Finset ArithmeticFunction
noncomputable section

/-- At fixed steps one vertex is injective in the first coordinate. Thus the
total von Mangoldt weight of its proper prime powers costs at most ψ(X)−θ(X).
The auxiliary weight bounds the product at the remaining vertices. -/
theorem proper_power_error {α : Type*} (S : Finset α) (f : α → ℕ) (w : α → ℝ)
    (X : ℕ) (one : 1 ≤ X) (K : ℝ)
    (inj : Set.InjOn f (S : Set α))
    (range : ∀ i ∈ S, 0 < f i ∧ f i ≤ X ∧ ¬(f i).Prime)
    (bound : ∀ i ∈ S, |w i| ≤ K) (kp : 0 ≤ K) :
    |∑ i ∈ S, vonMangoldt (f i) * w i| ≤ (2 * Real.sqrt X * Real.log X) * K := by
  classical
  have sub : S.image f ⊆ (Ioc 0 X).filter (fun n => ¬n.Prime) := by
    intro n h
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(range i hi).1,(range i hi).2.1⟩,(range i hi).2.2⟩
  have total : (∑ i ∈ S, vonMangoldt (f i)) ≤ 2 * Real.sqrt X * Real.log X := calc
    _ = ∑ n ∈ S.image f, vonMangoldt n := (sum_image inj).symm
    _ ≤ ∑ n ∈ (Ioc 0 X).filter (fun n => ¬n.Prime), vonMangoldt n :=
      sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => vonMangoldt_nonneg)
    _ = Chebyshev.psi X - Chebyshev.theta X := by
      simpa only [Nat.floor_natCast] using (Chebyshev.psi_sub_theta_eq_sum_not_prime (X:ℝ)).symm
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by exact_mod_cast one)
  calc
    _ ≤ ∑ i ∈ S, |vonMangoldt (f i) * w i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, vonMangoldt (f i) * K := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
      exact mul_le_mul_of_nonneg_left (bound i hi) vonMangoldt_nonneg
    _ = (∑ i ∈ S, vonMangoldt (f i)) * K := (sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right total kp

end
end Sun28.ArtinCube
#print axioms Sun28.ArtinCube.proper_power_error
