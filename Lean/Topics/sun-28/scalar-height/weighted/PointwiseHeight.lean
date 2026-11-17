import WeightedHeight
import NormSector

namespace Sun28.ScalarDepth
open Height Sun28.Ordinary Sun28.ScalarHeight Sun28.ScalarLucas Sun28.WitnessHeight
open Sun28.HeightFibres Sun28.HeightFibres.Sharp Sun28.FiveMarkUnits Sun28.PointPencils
noncomputable section
set_option exponentiation.threshold 1200

/-- The full squarefree part is at most the cutoff primorial times the outside radical. -/
theorem twist_size (x : ℚ) : (scalarClass x).natAbs ≤ cutoffProduct*radical x := by
  simpa only [ScalarPencil.totalRadical_eq,radical] using class_bound x

/-- The squarefree part of the sum-of-two-squares row is controlled even with the old constants. -/
theorem circle_allowance {x : ℚ} {d w : ℕ} {u v p c : ℤ} (h : Circle x d w u v p c) :
    (d:ℝ)^24 ≤ glazerConstant24*(radical x:ℝ)^24 := by
  have nzero := Int.natAbs_pos.mpr (octic_twist x).1.ne_zero
  have dl := Nat.le_of_dvd (Nat.mul_pos (by decide : 0<30) nzero) h.octicSupport
  have dsmall : d≤30*(cutoffProduct*radical x) := dl.trans (Nat.mul_le_mul_left _ (twist_size x))
  have tr : heightRadical (beta x).num (beta x).den=cutoffProduct*radical x := ScalarPencil.totalRadical_eq x
  have od : oddProduct (beta x).num (beta x).den=radical x := by
    unfold oddProduct oddSupport radical
    rw [scalar_support_exact]
  have span := original_margin (beta x).num (beta x).den
  rw [tr,od] at span
  have ds : (d:ℝ) ≤ 30*((cutoffProduct*radical x:ℕ):ℝ) := by exact_mod_cast dsmall
  have bound := pow_le_pow_left₀ (show 0≤(d:ℝ) by positivity) ds 24
  rw [mul_pow] at bound
  exact bound.trans ((mul_le_mul_of_nonneg_right (by norm_num : (30:ℝ)^24≤2^810) (by positivity)).trans span)

/-- At height at most B the failure of the stated old estimate forces a small Gaussian squarefree kernel. -/
theorem exceptional_kernel {x : ℚ} {B : ℕ} (small : max x.num.natAbs x.den≤B)
    (failure : glazerConstant24*(radical x:ℝ)^24 < logHeight₁ (beta x))
    {d w : ℕ} {u v p c : ℤ} (h : Circle x d w u v p c) :
    (d:ℝ)^24 < 2*Real.log (B:ℝ)+4 := by
  have upper := ScalarPencil.beta_height x
  rw [Rat.logHeight₁_eq_log_max x] at upper
  have hp : 0 < max x.num.natAbs x.den := lt_of_lt_of_le x.den_pos (le_max_right ..)
  have lo := Real.log_le_log (by exact_mod_cast hp : (0:ℝ)<(max x.num.natAbs x.den:ℕ))
    (by exact_mod_cast small : ((max x.num.natAbs x.den:ℕ):ℝ)≤(B:ℝ))
  have own := circle_allowance h
  change logHeight₁ (beta x)≤2*Real.log ((max x.num.natAbs x.den:ℕ):ℝ)+4 at upper
  linarith only [upper,lo,failure,own]

end
end Sun28.ScalarDepth
#print axioms Sun28.ScalarDepth.twist_size
#print axioms Sun28.ScalarDepth.circle_allowance
#print axioms Sun28.ScalarDepth.exceptional_kernel
