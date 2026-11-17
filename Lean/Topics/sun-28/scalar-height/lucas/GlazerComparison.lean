import ScalarLucas
import NumeratorStage

/-! Logical inputs are the anchor, divisibility and numerator estimate from the
proof of Glazer et al., frozen v8, Theorem "Arithmetic interpretation". -/
namespace GlazerScalar
open Sun28.Ordinary Height
noncomputable section

theorem growth_at_abs {s t z : ℤ} (live : z≠0) (big : 12≤ s.natAbs)
    (eqn : lucas s t z=0) :
    ((s.natAbs:ℝ)/4)*Real.log (s.natAbs:ℝ) ≤ Real.log |(t:ℝ)| := by
  let a := s.natAbs
  have h : 12≤a := big
  have half : a≤2*(a-4) := by omega
  have small : 3≤a-1 := by omega
  have sq : a≤(a-1)^2 := by
    have m := Nat.mul_le_mul_left (a-1) small
    rw [pow_two]
    omega
  have bpos : (0:ℝ)<(a-1:ℕ) := by exact_mod_cast (show 0<a-1 by omega)
  have nonneg := Real.log_nonneg (show (1:ℝ)≤(a-1:ℕ) by exact_mod_cast (show 1≤a-1 by omega))
  have cmp := Real.log_le_log (show (0:ℝ)<a by exact_mod_cast (show 0<a by omega))
    (show (a:ℝ)≤((a-1:ℕ):ℝ)^2 by exact_mod_cast sq)
  rw [Real.log_pow] at cmp
  have halfR : (a:ℝ)≤2*((a-4:ℕ):ℝ) := by exact_mod_cast half
  have power := signed_lucas_power s t z live (by omega) eqn
  have logs := Real.log_le_log (pow_pos bpos (a-4))
    (show ((a-1:ℕ):ℝ)^(a-4)≤(t.natAbs:ℝ) by exact_mod_cast power)
  rw [Real.log_pow] at logs
  rw [←Int.cast_abs,←Nat.cast_natAbs]
  change ((a:ℝ)/4)*Real.log (a:ℝ) ≤ _
  calc
    _ ≤ ((a:ℝ)/4)*(2*Real.log (a-1:ℕ)) := mul_le_mul_of_nonneg_left (by simpa using cmp) (by positivity)
    _ = ((a:ℝ)/2)*Real.log (a-1:ℕ) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right (by linarith : (a:ℝ)/2≤(a-4:ℕ)) nonneg).trans logs

/-- The manuscript's numerical estimate, including the absorption of the additive six. -/
theorem numerator_log {B H N h : ℝ} (bpos : 0 < B) (cap : 6 ≤ H) (nlo : 1 ≤ N)
    (size : B^2 ≤ 7*H*N^(3/8:ℝ)+6) (num : N ≤ 2*Real.exp h*B) :
    Real.log B ≤ (8/13)*Real.log (16*H)+(3/13)*h := by
  have hp : 0 < H := by linarith
  have np : 0 < N := by linarith
  have pw : 1 ≤ N^(3/8:ℝ) := Real.one_le_rpow nlo (by norm_num)
  have margin : H ≤ H*N^(3/8:ℝ) := by
    simpa using mul_le_mul_of_nonneg_left pw hp.le
  have bound : B^2 ≤ (8*H)*N^(3/8:ℝ) := by linarith only [size,margin,cap]
  have logs := Real.log_le_log (pow_pos bpos 2) bound
  rw [Real.log_pow,Real.log_mul (mul_pos (by norm_num) hp).ne' (Real.rpow_pos_of_pos np _).ne',
    Real.log_rpow np] at logs
  have nlog := Real.log_le_log np num
  rw [Real.log_mul (by positivity) bpos.ne', Real.log_mul (by norm_num) (Real.exp_pos h).ne',
    Real.log_exp] at nlog
  have c : Real.log (16*H)=Real.log 2+Real.log (8*H) := by
    rw [←Real.log_mul (by norm_num) (by positivity)]; ring_nf
  rw [c]
  linarith only [logs,nlog,Real.log_nonneg (by norm_num : (1:ℝ)≤2)]

/-- The scalar bound suffices with the constants in the manuscript's numerator comparison. -/
theorem scalar_separation {H B : ℝ} {A R : ℕ} {s t z n : ℤ} {x : ℚ}
    (live : z≠0) (eqn : lucas s t z=0) (positive : 0<H)
    (large : 17≤A) (anchor : A≤ s.natAbs) (reserve : (20*H)^2≤(A:ℝ))
    (divides : R^48 ∣ s.natAbs)
    (scalar : let V : ℝ := max A (R^48); logHeight₁ (x^2+2)≤V*Real.log V)
    (upper : x^2+2≠(n:ℚ) → Real.log B ≤ (8/13)*Real.log (16*H)+(3/13)*logHeight₁ (x^2+2))
    (index : Real.log |(t:ℝ)|≤Real.log B) : x^2+2=(n:ℚ) ∧ ∃ k : ℤ, x=(k:ℚ) := by
  let a : ℝ := s.natAbs
  let V : ℕ := max A (R^48)
  have ap : 0<s.natAbs := by omega
  have vlow : 17≤V := large.trans (le_max_left ..)
  have vup : V≤ s.natAbs := max_le anchor (Nat.le_of_dvd ap divides)
  have vR : (V:ℝ)≤a := by dsimp only [a]; exact_mod_cast vup
  have lo : (17:ℝ)≤a := by dsimp only [a]; exact_mod_cast large.trans anchor
  have vp : (1:ℝ)<V := by exact_mod_cast (show 1<V by omega)
  have lv := Real.log_le_log (lt_trans zero_lt_one vp) vR
  have la : 0<Real.log a := Real.log_pos (by linarith)
  have cost := mul_le_mul vR lv (Real.log_nonneg vp.le) (by linarith : 0≤a)
  have height : logHeight₁ (x^2+2)≤a*Real.log a := by
    apply le_trans _ cost
    simpa only [V,Nat.cast_max,Nat.cast_pow] using scalar
  have anchorR : (A:ℝ)≤a := by dsimp only [a]; exact_mod_cast anchor
  have square : (16*H)^2≤a := by nlinarith only [reserve,anchorR,sq_nonneg H]
  have r := Real.log_le_log (pow_pos (mul_pos (by norm_num) positive) 2) square
  rw [Real.log_pow] at r
  have lower := growth_at_abs live (by omega) eqn
  change (a/4)*Real.log a ≤ _ at lower
  have eq : x^2+2=(n:ℚ) := by
    by_contra ne
    have surplus := mul_pos (show 0<a-16 by linarith) la
    have lower' : (1/4:ℝ)*(a*Real.log a)≤Real.log |(t:ℝ)| := by
      convert lower using 1
      ring
    have r' : (2:ℝ)*Real.log (16*H)≤Real.log a := by simpa using r
    have summed : a*Real.log a ≤ 16*Real.log a := by
      linarith only [upper ne,index,lower',height,r']
    linarith only [summed,show 0 < a*Real.log a-16*Real.log a by rwa [sub_mul] at surplus]
  refine ⟨eq,Sun28.integral_input x (2*n-1) ?_⟩
  push_cast
  linarith only [eq]

/-- For Glazer’s scalar x²+2 only the manuscript’s ordinary index bound remains as input here. -/
theorem scalar_of_index_bound (m : Fin 4 → ℤ) (x : ℚ) (H : ℝ) (A R : ℕ)
    (live : m 3≠0) (eqn : lucas (m 1) (m 2) (m 3)=0) (cap : 6≤H)
    (large : 17≤A) (anchor : A ≤ (m 1).natAbs) (reserve : (20*H)^2≤(A:ℝ))
    (divides : R^48 ∣ (m 1).natAbs)
    (scalar : let V : ℝ := max A (R^48); logHeight₁ (x^2+2)≤V*Real.log V)
    (size : x^2+2≠(m 0:ℚ) → (indexSize m)^2 ≤
      7*H*(((x^2+2-(m 0:ℚ)).num.natAbs:ℝ)^(3/8:ℝ))+6) :
    x^2+2=(m 0:ℚ) ∧ ∃ k : ℤ, x=(k:ℚ) := by
  have big := one_le_indexSize m
  have bp : 0 < indexSize m := lt_of_lt_of_le zero_lt_one big
  apply scalar_separation (A:=A) (R:=R) (H:=H) (B:=indexSize m) live eqn (by linarith)
    large anchor reserve divides scalar
  · intro wrong
    let β := x^2+2
    have jpos := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr (sub_ne_zero.mpr wrong))
    have ht := Sun28.IndexHeights.numerator_bound β (m 0)
    have i := abs_first_le_indexSize m
    apply numerator_log bp cap (by exact_mod_cast jpos) (size wrong)
    rw [logHeight₁_eq_log_mulHeight₁,Real.exp_log (mulHeight₁_pos _)]
    calc
      _ ≤ _ := ht
      _ ≤ (2*indexSize m)*mulHeight₁ β :=
        mul_le_mul_of_nonneg_right (by linarith only [i,big]) (mulHeight₁_pos β).le
      _ = _ := by dsimp only [β];ring
  · have power := signed_lucas_power _ _ _ live (large.trans anchor |> fun h => by omega) eqn
    have pos : 0 < |(m 2:ℝ)| := by
      rw [←Int.cast_abs,←Nat.cast_natAbs]
      exact_mod_cast (pow_pos (show 0<(m 1).natAbs-1 by omega) _).trans_le power
    exact Real.log_le_log pos (by simp [indexSize])

end
end GlazerScalar
#print axioms GlazerScalar.growth_at_abs
#print axioms GlazerScalar.scalar_separation

#print axioms GlazerScalar.numerator_log
#print axioms GlazerScalar.scalar_of_index_bound
