import HeightReduction

namespace Sun28.ConicArithmetic
open Height ZInQ ZInQ.Mult Sun28.ScalarHeight Sun28.Ordinary Sun28.ConicCovers
open Sun28.ScalarRankZero Sun28.ScalarDepth Sun28.Forward Sun28.WitnessHeight
open Sun28.FixedPreparation Sun28.ScalarLucas Sun28.WitnessIndices Sun28.IndexHeights Sun28.FactorHeights
noncomputable section
attribute [local irreducible] fixedMultiplier floor allowance Sun28.Ordinary.glazerConstant24
set_option maxRecDepth 12000

private theorem lead_bound (a b p:ℝ) (ha:0≤a) (hb:0≤b) (hp:1≤p) :
    a ≤ 2*(a+b)*p^24+128 := by
  have prod:=le_mul_of_one_le_right (show 0≤2*(a+b) by positivity) (one_le_pow₀ hp (n:=24))
  linarith only [ha,hb,prod]

theorem explicit_cap : (4608:ℝ)^331776 ≤ heightCap := by
  have p1:1≤∏p∈oldCutoff,(p:ℝ) := Finset.one_le_prod₀ (by
    intro p mem
    have prime:Nat.Prime p:=(Finset.mem_filter.mp (show p∈(Finset.range 76177).filter Nat.Prime from mem)).2
    exact_mod_cast prime.one_lt.le)
  have pos:0≤(4608:ℝ)^165888:=pow_nonneg (by norm_num) _
  have lead:(4608:ℝ)^165888 ≤ glazerConstant24 := by
    unfold glazerConstant24
    exact lead_bound _ _ _ pos (pow_nonneg (by norm_num: (0:ℝ)≤6) _) p1
  calc
    (4608:ℝ)^331776 = ((4608:ℝ)^165888)^2 := pow_mul (4608:ℝ) 165888 2
    _ ≤ glazerConstant24^2 := pow_le_pow_left₀ pos lead 2
    _ ≤ heightCap := by
      have logc : Real.log 31213 ≤ 31213 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
      have big : (128:ℝ) ≤ glazerConstant24 := by
        unfold glazerConstant24
        change 128≤2*((4608:ℝ)^165888+6^100)*(∏p∈oldCutoff,(p:ℝ))^24+128
        exact le_add_of_nonneg_left (by positivity)
      have H2:16384≤glazerConstant24^2 := by nlinarith only [sq_nonneg (glazerConstant24-128),big]
      have mult : 216*glazerConstant24^2 < (fixedMultiplier:ℝ) := fixed_reserve.2.2
      unfold heightCap
      linarith only [H2,mult,logc]

end
end Sun28.ConicArithmetic
#print axioms Sun28.ConicArithmetic.explicit_cap
