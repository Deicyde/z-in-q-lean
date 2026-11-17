import UnitNumerator

namespace Sun28.ScalarPencil
open Sun28.WitnessHeight Sun28.ScalarHeight Sun28.Ordinary Sun28.FiveMarkUnits
open Sun28.HeightFibres Sun28.HeightFibres.Sharp ZInQ.RouteK Height
noncomputable section
set_option exponentiation.threshold 1000

/-- A square first row gives a positive gap between integer squares. -/
theorem denominator_gap {x:ℚ} (nonzero:x≠0) (square:IsSquare (x^2+1)) :
    2*x.den<x.num.natAbs^2:=by
  obtain ⟨r,h⟩:=square
  have bn:(x.den:ℚ)≠0:=by exact_mod_cast x.den_nz
  have q: ((x.num.natAbs^2+x.den^2:ℕ):ℚ)=(r*(x.den:ℚ))^2:=by
    push_cast
    rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs,sq_abs]
    rw [←x.num_div_den] at h
    field_simp at h
    linear_combination h
  obtain ⟨z,eq⟩:=Rat.isSquare_natCast_iff.mp (show IsSquare ((x.num.natAbs^2+x.den^2:ℕ):ℚ) from
    ⟨r*(x.den:ℚ),q.trans (pow_two _)⟩)
  have pa:=Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr nonzero)
  have pos:0<x.num.natAbs^2:=pow_pos pa _
  have zgt:x.den<z:=by
    by_contra! low
    have le:=Nat.mul_le_mul low low
    nlinarith only [le,eq,pos]
  have inc:=Nat.mul_le_mul zgt zgt
  nlinarith only [inc,eq]

/-- The height on this conic is bounded by the numerator alone. -/
theorem pythagorean_height {x:ℚ} (nonzero:x≠0) (square:IsSquare (x^2+1)) :
    logHeight₁ (beta x)≤4*numberLog x.num+4:=by
  have gap:=denominator_gap nonzero square
  have pa:=Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr nonzero)
  have hn:x.num.natAbs≤x.num.natAbs^2:=by
    simpa using pow_le_pow_right₀ (show 1≤x.num.natAbs from pa) (by decide:1≤2)
  have den:x.den≤x.num.natAbs^2:=by omega
  have cap:max x.num.natAbs x.den≤x.num.natAbs^2:=max_le hn den
  have top:0<(max x.num.natAbs x.den:ℕ):=lt_of_lt_of_le pa (le_max_left ..)
  have lg:=Real.log_le_log (show 0<((max x.num.natAbs x.den:ℕ):ℝ) by exact_mod_cast top)
    (show ((max x.num.natAbs x.den:ℕ):ℝ)≤(x.num.natAbs:ℝ)^2 by exact_mod_cast cap)
  rw [Real.log_pow] at lg
  have base:=beta_height x
  rw [Rat.logHeight₁_eq_log_max x] at base
  change Real.log ((max x.num.natAbs x.den:ℕ):ℝ)≤_ at lg
  norm_num only [Nat.cast_ofNat] at lg
  change logHeight₁ (beta x)≤4*Real.log (x.num.natAbs:ℝ)+4
  linarith only [base,lg]

theorem pythagorean_sector {x:ℚ} (nonzero:x≠0) (square:IsSquare (x^2+1))
    (bound:numberLog x.num≤(totalRadical x:ℝ)^24) :
    logHeight₁ (beta x)≤glazerConstant24*(primeProduct (scalarPrimes x):ℝ)^24 := by
  have h:=pythagorean_height nonzero square
  have t:1≤(totalRadical x:ℝ):=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd _ _))
  have direct:logHeight₁ (beta x)≤2^810*(totalRadical x:ℝ)^24:=by
    linarith only [bound,h,one_le_pow₀ t (n:=24)]
  have eq:oddProduct (beta x).num (beta x).den=primeProduct (scalarPrimes x):=by
    simp only [oddProduct,oddSupport,scalar_support_exact]
  exact direct.trans (eq ▸ original_margin (beta x).num (beta x).den)
end
end Sun28.ScalarPencil
#print axioms Sun28.ScalarPencil.denominator_gap
#print axioms Sun28.ScalarPencil.pythagorean_height
#print axioms Sun28.ScalarPencil.pythagorean_sector
