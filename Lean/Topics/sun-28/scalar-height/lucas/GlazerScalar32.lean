import GlazerComparison

/-! The order-32 scalar step in the fixed rational source of the v8 manuscript. -/
namespace GlazerScalar
open Sun28.Ordinary Height
noncomputable section

theorem numerator_log32 {B H N h : ℝ} (bp : 0 < B) (cap : 6 ≤ H) (nlo : 1 ≤ N)
    (size : B^2 ≤ 7*H*N^(3/2:ℝ)+6) (num : N ≤ 2*Real.exp h*B) :
    Real.log B ≤ 2*Real.log (32*H)+3*h := by
  have hp : 0 < H := by linarith
  have np : 0 < N := by linarith
  have pw : 1 ≤ N^(3/2:ℝ) := Real.one_le_rpow nlo (by norm_num)
  have margin : H ≤ H*N^(3/2:ℝ) := by simpa using mul_le_mul_of_nonneg_left pw hp.le
  have bound : B^2 ≤ (8*H)*N^(3/2:ℝ) := by linarith only [size,margin,cap]
  have logs := Real.log_le_log (pow_pos bp 2) bound
  rw [Real.log_pow,Real.log_mul (mul_pos (by norm_num) hp).ne' (Real.rpow_pos_of_pos np _).ne',
    Real.log_rpow np] at logs
  have nlog := Real.log_le_log np num
  rw [Real.log_mul (by positivity) bp.ne',Real.log_mul (by norm_num) (Real.exp_pos h).ne',
    Real.log_exp] at nlog
  have c : Real.log (32*H)=2*Real.log 2+Real.log (8*H) := by
    rw [show 32*H=2^2*(8*H) by ring,Real.log_mul (by norm_num) (by positivity),Real.log_pow]
    norm_num
  rw [c]
  linarith only [logs,nlog,Real.log_nonneg (by norm_num : (1:ℝ)≤2)]

theorem scalar32_of_index_bound (m : Fin 4 → ℤ) (x : ℚ) (H : ℝ) (M R : ℕ)
    (live : m 3≠0) (eqn : lucas (m 1) (m 2) (m 3)=0) (cap : 6≤H)
    (nz : m 1≠0) (large : 17≤M) (reserve : (32*H)^2≤(M:ℝ))
    (anchor : M ∣ (m 1).natAbs) (divides : R^32 ∣ (m 1).natAbs)
    (scalar : let L : ℝ := M.lcm (R^32); logHeight₁ (x^2+2)≤L*Real.log L/24)
    (size : x^2+2≠(m 0:ℚ) → (indexSize m)^2 ≤
      7*H*(((x^2+2-(m 0:ℚ)).num.natAbs:ℝ)^(3/2:ℝ))+6) :
    x^2+2=(m 0:ℚ) ∧ ∃ k : ℤ, x=(k:ℚ) := by
  let a : ℝ := (m 1).natAbs
  let L := M.lcm (R^32)
  have ap := Int.natAbs_pos.mpr nz
  have rp : R≠0 := by intro z;subst R;simp [nz] at divides
  have ml : M≤L := Nat.le_of_dvd (Nat.lcm_pos (by omega) (pow_pos (Nat.pos_of_ne_zero rp) 32)) (Nat.dvd_lcm_left ..)
  have la : L≤(m 1).natAbs := Nat.le_of_dvd ap (Nat.lcm_dvd anchor divides)
  have mlR : (M:ℝ)≤L := by exact_mod_cast ml
  have laR : (L:ℝ)≤a := by dsimp only [a];exact_mod_cast la
  have lo : (17:ℝ)≤L := by exact_mod_cast large.trans ml
  have lp : (0:ℝ)<L := by linarith
  have cost := mul_le_mul laR (Real.log_le_log lp laR)
    (Real.log_nonneg (by linarith : (1:ℝ)≤L)) (by linarith : 0≤a)
  have height : logHeight₁ (x^2+2)≤a*Real.log a/24 := le_trans scalar (div_le_div_of_nonneg_right cost (by norm_num))
  have r := Real.log_le_log (pow_pos (show 0 < 32*H by linarith) 2)
    (reserve.trans (mlR.trans laR))
  rw [Real.log_pow] at r
  norm_num1 at r
  have bg : 12≤(m 1).natAbs := by omega
  have lower := growth_at_abs live bg eqn
  change (a/4)*Real.log a ≤ _ at lower
  have lower' : (1/4:ℝ)*(a*Real.log a)≤Real.log |(m 2:ℝ)| := by
    convert lower using 1
    ring
  have pow := signed_lucas_power _ _ _ live (by omega) eqn
  have tp : 0 < |(m 2:ℝ)| := by
    rw [←Int.cast_abs,←Nat.cast_natAbs]
    exact_mod_cast (pow_pos (show 0<(m 1).natAbs-1 by omega) _).trans_le pow
  have index := Real.log_le_log tp (show |(m 2:ℝ)| ≤ indexSize m by simp [indexSize])
  have eq : x^2+2=(m 0:ℚ) := by
    by_contra ne
    let β:=x^2+2
    have npos := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr (sub_ne_zero.mpr ne))
    have big := one_le_indexSize m
    have num := Sun28.IndexHeights.numerator_bound β (m 0)
    have ni := abs_first_le_indexSize m
    have up : Real.log (indexSize m)≤2*Real.log (32*H)+3*logHeight₁ β := by
      apply numerator_log32 (lt_of_lt_of_le zero_lt_one big) cap (by exact_mod_cast npos) (size ne)
      rw [logHeight₁_eq_log_mulHeight₁,Real.exp_log (mulHeight₁_pos _)]
      calc
        _ ≤ _ := num
        _ ≤ (2*indexSize m)*mulHeight₁ β :=
          mul_le_mul_of_nonneg_right (by linarith only [ni,big]) (mulHeight₁_pos β).le
        _ = _ := by ring
    dsimp only [β] at up
    have s : a*Real.log a≤8*Real.log a := by
      linarith only [lower',r,up,index,height]
    have strict := mul_lt_mul_of_pos_right (by linarith only [lo,laR] : (8:ℝ)<a)
      (Real.log_pos (by linarith only [lo,laR] : 1<a))
    exact (not_lt_of_ge s) strict
  refine ⟨eq,Sun28.integral_input x (2*(m 0)-1) ?_⟩
  push_cast
  linarith only [eq]

end
end GlazerScalar
#print axioms GlazerScalar.numerator_log32
#print axioms GlazerScalar.scalar32_of_index_bound
