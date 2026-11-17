import PellField

/-! Elementary numerical bounds for the archimedean simultaneous Pell estimate. -/
namespace Sun28.HeightFibres
noncomputable section

/-- Constants are deliberately rounded upwards. They hold from T=1 on. -/
theorem regulator_estimate {D T reg : ℝ} (one : 1≤T) (d : 1≤D) (dp : D≤64*T^6)
    (r : reg≤D*(logStar D)^3) : reg≤2^18*T^9 := by
  have t : 0<T:=by linarith
  have l2:=Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
  have l64 : Real.log 64≤6 := by
    rw [show (64:ℝ)=2^6 by norm_num,Real.log_pow]
    norm_num
    linarith
  have ld:=Real.log_le_log (by linarith : 0<D) dp
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ t.ne'),Real.log_pow] at ld
  have lt:=Real.log_le_sub_one_of_pos t
  have star : logStar D≤12*T := max_le (by linarith) (by norm_num at ld;linarith only [ld,l64,lt,one])
  calc
    reg ≤ D*(logStar D)^3 := r
    _ ≤ (64*T^6)*(12*T)^3 := mul_le_mul dp (pow_le_pow_left₀ (le_trans (by norm_num : (0:ℝ)≤1) (le_max_left _ _)) star 3) (pow_nonneg (le_trans (by norm_num : (0:ℝ)≤1) (le_max_left _ _)) 3) (by positivity)
    _ ≤ 2^18*T^9 := by nlinarith only [pow_nonneg t.le 9]

/-- A positive-regulator, degree-four Pell bound becomes a uniform polynomial
in the full odd radical and a linear function of the logarithm of its right side. -/
theorem pell_numeric {T reg J h : ℝ} (one : 1≤T) (rp : 0<reg) (r : reg≤2^18*T^9)
    (jp : 0≤J) (bound : h≤(2:ℝ)^140*reg*(1+logStar reg)*(reg+4*Real.log T+J)) :
    h ≤ 2^185*T^19+2^165*T^10*J := by
  have t : 0<T:=by linarith
  have l2:=Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
  have l:=Real.log_le_log rp r
  rw [Real.log_mul (by positivity) (pow_ne_zero _ t.ne'),Real.log_pow,Real.log_pow] at l
  norm_num at l
  have lt:=Real.log_le_sub_one_of_pos t
  have star : logStar reg≤32*T := max_le (by linarith) (by linarith only [l,l2,lt,one])
  have t9 : T≤T^9 := by simpa using pow_le_pow_right₀ one (by decide : 1≤9)
  have u : 1+logStar reg≤64*T := by linarith
  have v : reg+4*Real.log T+J≤2^19*T^9+J := by linarith only [r,lt,t9,one]
  have v0 : 0≤reg+4*Real.log T+J := by linarith only [rp,Real.log_nonneg one,jp]
  have u0 : 0≤1+logStar reg := by have := le_max_left (1:ℝ) (Real.log reg);unfold logStar;linarith
  calc
    h ≤ _ := bound
    _ ≤ (2:ℝ)^140*(2^18*T^9)*(64*T)*(2^19*T^9+J) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left r (by positivity)) u u0 (by positivity)) v v0 (by positivity)
    _ ≤ 2^185*T^19+2^165*T^10*J := by nlinarith only [pow_nonneg t.le 19,mul_nonneg (pow_nonneg t.le 10) jp]

end
end Sun28.HeightFibres
#print axioms Sun28.HeightFibres.regulator_estimate
#print axioms Sun28.HeightFibres.pell_numeric
