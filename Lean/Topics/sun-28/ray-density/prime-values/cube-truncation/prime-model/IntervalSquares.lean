import GaussianWindow

namespace Sun28.PrimeModel
open Finset Sun28.AffinePullback
noncomputable section
variable {n : ℕ} [NeZero n]

/-- The order-one difference sum is a sum of squares of interval sums. -/
theorem interval_squares (J : ℕ) (f : ZMod n → ℝ) :
    boxSum n 1 [J] f = ∑ x : ZMod n, (∑ i ∈ range J, f (x+i))^2 := by
  classical
  have translated (i j : ℕ) :
      (∑ x : ZMod n, f x * f (x+((i:ℤ)-j:ℤ))) =
        ∑ x : ZMod n, f (x+j)*f (x+i) := by
    let F (x : ZMod n) := f x * f (x+((i:ℤ)-j:ℤ))
    have shift := Equiv.sum_comp (Equiv.addRight (j:ZMod n)) F
    change (∑ x : ZMod n, F x) = _
    rw [←shift]
    apply sum_congr rfl
    intro x _
    change f (x+j)*f (x+j+((i:ℤ)-j:ℤ)) = _
    push_cast
    rw [show x+j+((i:ZMod n)-j)=x+i by ring]
  simp only [boxSum, Nat.cast_one, one_mul]
  simp_rw [translated]
  calc
    _ = ∑ i ∈ range J, ∑ x : ZMod n, ∑ j ∈ range J, f (x+j)*f (x+i) := by
      apply sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ x : ZMod n, ∑ i ∈ range J, ∑ j ∈ range J, f (x+j)*f (x+i) := Finset.sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro x _
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]

/-- The localized order-two cube is a sum of nonnegative terms even for signed weights. -/
theorem two_squares (J : ℕ) (f : ZMod n → ℝ) :
    boxSum n 1 [J,J] f =
      ∑ i ∈ range J, ∑ j ∈ range J, ∑ x : ZMod n,
        (∑ v ∈ range J, f (x+v)*f (x+v+((i:ℤ)-j:ℤ)))^2 := by
  rw [boxSum]
  simp only [Nat.cast_one, one_mul, interval_squares]

end
end Sun28.PrimeModel
#print axioms Sun28.PrimeModel.interval_squares
#print axioms Sun28.PrimeModel.two_squares
