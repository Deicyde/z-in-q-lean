import Mathlib

/-! Explicit one-dimensional envelopes for integer and half-integer Gaussian sums. -/
namespace ZInQBlueprint.PeriodGaussian
noncomputable section
open Real

def offset (s : Bool) : ℝ := if s then 1/2 else 0

def envelope (s : Bool) (b : ℝ) : ℤ → ℝ
  | .ofNat n => if s then exp (-b/4) * (1/13)^n else (3/11)^n
  | .negSucc n => if s then exp (-b/4) * (1/13)^n else (3/11)^(n+1)

def mass (s : Bool) (b : ℝ) : ℝ := if s then (13/6)*exp (-b/4) else 7/4

theorem envelope_nonneg (s : Bool) (b : ℝ) (n : ℤ) : 0 ≤ envelope s b n := by
  cases n <;> cases s <;> simp [envelope] <;> positivity

theorem envelope_hasSum (s : Bool) (b : ℝ) : HasSum (envelope s b) (mass s b) := by
  have q : HasSum (fun n : ℕ => (3/11:ℝ)^n) (11/8) := by
    convert hasSum_geometric_of_lt_one (r:=3/11) (by norm_num) (by norm_num) using 1; norm_num
  have r : HasSum (fun n : ℕ => (1/13:ℝ)^n) (13/12) := by
    convert hasSum_geometric_of_lt_one (r:=1/13) (by norm_num) (by norm_num) using 1; norm_num
  cases s
  · have neg : HasSum (fun n : ℕ => (3/11:ℝ)^(n+1)) (3/8) := by
      convert q.mul_right (3/11) using 1 <;> simp [pow_succ]
    rw [show mass false b = 11/8 + 3/8 by norm_num [mass]]
    exact HasSum.of_nat_of_neg_add_one q neg
  · have h := r.mul_left (exp (-b/4))
    rw [show mass true b = exp (-b/4) * (13/12) + exp (-b/4) * (13/12) by
      simp [mass]; ring]
    exact HasSum.of_nat_of_neg_add_one h h

private theorem exp_drop {b : ℝ} (hb : 4/3 ≤ b) : exp (-b) ≤ 3/11 := by
  have e : (2.7 : ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have h : (11/3:ℝ)^3 < (exp (4/3))^3 := calc
    _ < (2.7:ℝ)^4 := by norm_num
    _ < (exp 1)^4 := pow_lt_pow_left₀ e (by norm_num) (by decide)
    _ = (exp (4/3))^3 := by rw [← exp_nat_mul, ← exp_nat_mul]; norm_num
  have lower : 11/3 ≤ exp b := (le_of_lt (lt_of_pow_lt_pow_left₀ 3 (by positivity) h)).trans (exp_le_exp.mpr hb)
  rw [exp_neg, inv_eq_one_div, div_le_iff₀ (exp_pos _)]
  linarith

theorem width_of_reduced {y : ℝ} (hy : sqrt (3/4) ≤ y) : 4/3 ≤ π*y/2 := by
  have hs : (0.85:ℝ) ≤ sqrt (3/4) := by
    nlinarith [Real.sq_sqrt (show (0:ℝ)≤3/4 by norm_num), Real.sqrt_nonneg (3/4)]
  have h := mul_le_mul Real.pi_gt_d2.le (hs.trans hy) (by norm_num) Real.pi_pos.le
  linarith

private theorem unshifted (b : ℝ) (hb : 4/3 ≤ b) (n : ℕ) :
    exp (-b*(n:ℝ)^2) ≤ (3/11)^n := by
  have hn : (n:ℝ) ≤ (n:ℝ)^2 := by
    cases n with
    | zero => norm_num
    | succ m => push_cast; nlinarith [sq_nonneg (m:ℝ)]
  calc
    _ ≤ exp ((n:ℝ)*(-b)) := exp_le_exp.mpr (by nlinarith [mul_nonneg (show 0≤b by linarith) (sub_nonneg.mpr hn)])
    _ = (exp (-b))^n := exp_nat_mul _ _
    _ ≤ _ := pow_le_pow_left₀ (exp_pos _).le (exp_drop hb) _

private theorem shifted (b : ℝ) (hb : 4/3 ≤ b) (n : ℕ) :
    exp (-b*((n:ℝ)+1/2)^2) ≤ exp (-b/4)*(1/13)^n := by
  have hn : (n:ℝ) ≤ (n:ℝ)^2 := by
    cases n with
    | zero => norm_num
    | succ m => push_cast; nlinarith [sq_nonneg (m:ℝ)]
  have h2 : exp (-2*b) ≤ 1/13 := by
    calc
      _ = (exp (-b))^2 := by rw [← exp_nat_mul]; norm_num
      _ ≤ (3/11:ℝ)^2 := pow_le_pow_left₀ (exp_pos _).le (exp_drop hb) _
      _ ≤ _ := by norm_num
  calc
    _ ≤ exp (-b/4+(n:ℝ)*(-2*b)) := exp_le_exp.mpr (by
      nlinarith [mul_nonneg (show 0≤b by linarith) (sub_nonneg.mpr hn)])
    _ = exp (-b/4)*exp (-2*b)^n := by rw [exp_add,exp_nat_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (exp_pos _).le h2 _) (exp_pos _).le

theorem gaussian_le_envelope (s : Bool) {b : ℝ} (hb : 4/3 ≤ b) (n : ℤ) :
    exp (-b*((n:ℝ)+offset s)^2) ≤ envelope s b n := by
  cases n with
  | ofNat n =>
    cases s
    · simpa [offset,envelope] using unshifted b hb n
    · simpa [offset,envelope] using shifted b hb n
  | negSucc n =>
    cases s
    · have h := unshifted b hb (n+1)
      simpa only [offset,Bool.false_eq_true,ite_false,add_zero,envelope,Int.cast_negSucc,
        Nat.cast_add, Nat.cast_one, ← neg_add, even_two.neg_pow] using h
    · change exp (-b*((Int.negSucc n : ℤ)+ (1/2:ℝ))^2) ≤ exp (-b/4)*(1/13)^n
      rw [Int.cast_negSucc, Nat.cast_add,Nat.cast_one, show -((n:ℝ)+1) + 1/2 = -((n:ℝ)+1/2) by ring, even_two.neg_pow]
      exact shifted b hb n

end
end ZInQBlueprint.PeriodGaussian
#print axioms ZInQBlueprint.PeriodGaussian.gaussian_le_envelope
#print axioms ZInQBlueprint.PeriodGaussian.envelope_hasSum
#print axioms ZInQBlueprint.PeriodGaussian.width_of_reduced
