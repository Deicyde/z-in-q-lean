import FiniteCharts
import ScalarEstimates

namespace Sun28.FactorHeights
open Sun28.Ordinary Sun28.ScalarHeight Height
noncomputable section

/-- Both three-conic systems contain a split difference of squares. -/
theorem split_pencils {x:ℚ} (point:conics x 2 1 1 ∨ conics x 14 (-35) 7) :
    ∃u w:ℚ, u≠0 ∧ w≠0 ∧
    ((2*x^2+3=2*u^2 ∧ (w-8*u)*(w+8*u)=343) ∨
     (2*x^2+3=14*u^2 ∧ (w-8*u)*(w+8*u)=49)) := by
  rcases point with ⟨u,v,w,un,_,wn,e,_,f⟩|⟨u,v,w,un,_,wn,e,_,f⟩
  · norm_num at e f
    exact ⟨u,w,un,wn,Or.inl ⟨e,by linear_combination 32*e-f⟩⟩
  · norm_num at e f
    exact ⟨u,w,un,wn,Or.inr ⟨e,by linear_combination (32*e-f)/7⟩⟩

private theorem height_bound (x:ℚ) {K m:ℕ} (kp:0<K) (mpos : 0 < m)
    (bound:x.num.natAbs≤K*x.den^m) :
    logHeight₁ (beta x)≤2*Real.log (K:ℝ)+2*m*Real.log (x.den:ℝ)+4:=by
  have q:=Sun28.ScalarPencil.beta_height x
  have d:=x.den_pos
  have den:x.den≤x.den^m:=by simpa using (pow_le_pow_right₀ (show 1 ≤ x.den from d) (show 1 ≤ m from mpos))
  have maxb:max x.num.natAbs x.den≤K*x.den^m:=max_le bound (den.trans (Nat.le_mul_of_pos_left _ kp))
  have pos : 0 < max x.num.natAbs x.den:=d.trans_le (le_max_right ..)
  have le:=Real.log_le_log (Nat.cast_pos.mpr pos)
    (show ((max x.num.natAbs x.den:ℕ):ℝ)≤(K:ℝ)*(x.den:ℝ)^m by exact_mod_cast maxb)
  rw [Real.log_mul (Nat.cast_pos.mpr kp).ne' (pow_pos (Nat.cast_pos.mpr d) _).ne',Real.log_pow] at le
  rw [←Rat.logHeight₁_eq_log_max x] at le
  linarith only [q,le]

/-- In the positive system a difference of two integral squares controls the
original rational numerator by the square of its denominator. -/
theorem positive_height {x:ℚ} (h:conics x 2 1 1) :
    logHeight₁ (beta x)≤2*Real.log 1199+4*Real.log x.den+4 := by
  obtain ⟨u,v,w,_,_,_,_,ev,_⟩:=h
  have b0:(x.den:ℚ)≠0:=by exact_mod_cast x.den_nz
  have id:(x.num:ℚ)=x*x.den:=(div_eq_iff b0).mp x.num_div_den
  have eq : IsSquare ((x.num^2-1199*(x.den:ℤ)^2:ℤ):ℚ):=by
    refine ⟨v*x.den,?_⟩
    push_cast;rw [id];norm_num at ev
    linear_combination (x.den:ℚ)^2*ev
  obtain ⟨q,qeq⟩:=Rat.isSquare_intCast_iff.mp eq
  let a:=x.num.natAbs
  let b:=x.den
  let z:=q.natAbs
  have pq:(a:ℤ)^2=1199*(b:ℤ)^2+(z:ℤ)^2:=by
    dsimp [a,b,z];rw [Int.natCast_natAbs,Int.natCast_natAbs,sq_abs,sq_abs]
    nlinarith only [qeq]
  have az:z<a:=by
    by_contra! e
    have n:0<(b:ℤ)^2:=by dsimp [b];positivity
    have sq:=pow_le_pow_left₀ (Int.natCast_nonneg a) (by exact_mod_cast e:(a:ℤ)≤(z:ℤ)) 2
    omega
  have gap:(z:ℤ)+1≤(a:ℤ):=by exact_mod_cast az
  have cap:(a:ℤ)≤1199*(b:ℤ)^2:=by
    nlinarith only [pq,mul_nonneg (show 0≤(a:ℤ)-(z:ℤ)-1 by omega)
      (show 0≤(a:ℤ)+(z:ℤ) by positivity),Int.natCast_nonneg z]
  convert height_bound x (K:=1199) (m:=2) (by decide) (by decide) (by exact_mod_cast cap) using 1; norm_num

/-- In the negative system the third binary form is negative: the real
bound already gives a linear, instead of quadratic, numerator bound. -/
theorem negative_height {x:ℚ} (h:conics x 14 (-35) 7) :
    logHeight₁ (beta x)≤2*Real.log 35+2*Real.log x.den+4 := by
  obtain ⟨u,v,w,_,_,_,_,ev,_⟩:=h
  have b0:(x.den:ℚ)≠0:=by exact_mod_cast x.den_nz
  have id:(x.num:ℚ)=x*x.den:=(div_eq_iff b0).mp x.num_div_den
  have cap:x^2≤1199:=by norm_num at ev;nlinarith only [ev,sq_nonneg v]
  have sqcap : (x.num:ℚ)^2≤1199*(x.den:ℚ)^2:=by
    rw [id,mul_pow];exact mul_le_mul_of_nonneg_right cap (sq_nonneg _)
  have bound:x.num.natAbs≤35*x.den:=by
    by_contra! big
    have sl:=mul_self_lt_mul_self (show (0:ℚ)≤35*x.den by positivity)
      (by exact_mod_cast big : (35:ℚ)*x.den<x.num.natAbs)
    have absid:((x.num.natAbs:ℕ):ℚ)=|(x.num:ℚ)|:=by rw [←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
    rw [absid,←pow_two] at sl
    rw [←pow_two,sq_abs] at sl
    nlinarith only [sl,sqcap,sq_nonneg (x.den:ℚ)]
  simpa using height_bound x (K:=35) (m:=1) (by decide) (by decide) (by simpa using bound)

end
end Sun28.FactorHeights
#print axioms Sun28.FactorHeights.split_pencils
#print axioms Sun28.FactorHeights.positive_height
#print axioms Sun28.FactorHeights.negative_height
