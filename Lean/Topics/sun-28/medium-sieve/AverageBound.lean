import MeanDivisors

namespace Sun28.MediumSieve
open Finset
open scoped Classical
noncomputable section

private theorem count_multiples (W m : ℕ) :
    ((Icc 1 W).filter (fun v=>m∣v)).card=W/m := by
  rw [←Nat.card_multiples' W m]
  congr 1
  ext v
  simp only [mem_filter,mem_Icc,mem_range]
  omega

theorem mean_square_divisors (W : ℕ) :
    (∑ v∈Icc 1 W,((v^2).divisors.card:ℝ))≤W*(harmonic W:ℝ)^2 := by
  let I:=Icc 1 W
  have rows (v : ℕ) : ((cells W v).card:ℝ) =
      ∑ z∈I ×ˢ I,if z.1*z.2∣v then (1:ℝ) else 0 := by
    simp [cells,I]
  have columns (z : ℕ×ℕ) :
      (∑ v∈I,if z.1*z.2∣v then (1:ℝ) else 0) ≤ (W:ℝ)/((z.1:ℝ)*z.2) := by
    have h : (∑ v∈I,if z.1*z.2∣v then (1:ℝ) else 0) =
        (((I.filter (fun v=>z.1*z.2∣v)).card:ℕ):ℝ) := by simp
    rw [h,count_multiples]
    simpa using (Nat.cast_div_le (α:=ℝ) (m:=W) (n:=z.1*z.2))
  have harm : (∑ a∈I, (a:ℝ)⁻¹)=(harmonic W:ℝ) := by
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    simp [I]
  calc
    _ ≤ ∑ v∈I,((cells W v).card:ℝ) := by
      apply sum_le_sum;intro v hv
      exact_mod_cast square_divisors (mem_Icc.mp hv).1 (mem_Icc.mp hv).2
    _ = ∑ z∈I ×ˢ I,∑ v∈I,if z.1*z.2∣v then (1:ℝ) else 0 := by simp_rw [rows];rw [sum_comm]
    _ ≤ ∑ z∈I ×ˢ I,(W:ℝ)/((z.1:ℝ)*z.2) := sum_le_sum fun z _=>columns z
    _ = (W:ℝ)*(harmonic W:ℝ)^2 := by
      have point (a b : ℕ) : (W:ℝ)/((a:ℝ)*b)=
          ((W:ℝ)*(a:ℝ)⁻¹)*(b:ℝ)⁻¹ := by simp [div_eq_mul_inv]; ring
      rw [sum_product]
      simp_rw [point,←mul_sum,harm]
      rw [←sum_mul,←mul_sum,harm];ring

theorem mean_gap (g : ℤ) (W : ℕ) :
    (∑ v∈Icc 1 W,(((g*(v:ℤ)^2).natAbs.divisors.card:ℕ):ℝ)) ≤
      g.natAbs.divisors.card*W*(harmonic W:ℝ)^2 := by
  calc
    _ ≤ ∑ v∈Icc 1 W, (g.natAbs.divisors.card:ℝ)*((v^2).divisors.card:ℝ) := by
      apply sum_le_sum
      intro v _
      simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast]
      exact_mod_cast divisor_submult g.natAbs (v^2)
    _ ≤ (g.natAbs.divisors.card:ℝ)*((W:ℝ)*(harmonic W:ℝ)^2) := by
      rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (mean_square_divisors W) (Nat.cast_nonneg _)
    _ = _ := by ring
end
end Sun28.MediumSieve
#print axioms Sun28.MediumSieve.mean_square_divisors
#print axioms Sun28.MediumSieve.mean_gap
