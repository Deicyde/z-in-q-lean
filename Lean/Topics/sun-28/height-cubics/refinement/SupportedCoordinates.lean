import SupportedCurve

namespace Sun28.HeightCubics.Refinement
open Sun28.FiveMarkUnits ZInQBlueprint.TwistDescent Height
open private height_div int_height from ContactHeight
noncomputable section

/-- From the rational j-invariant estimate we recover both heights in the
supported coefficient specialization of von Känel, Corollary 7.4. -/
theorem supported_coordinates (pub:PublishedElliptic) : Ordinate.PublishedCoordinates := by
  intro S a x y primes an supp ix iy eq
  let M₀:=62208*(primeProduct S)^2
  let M:ℝ:=M₀
  let W:=cleared x y
  obtain ⟨nz,J⟩:=cleared_j x y an eq
  obtain ⟨data⟩:=pub W nz
  have pS:0<primeProduct S:=Nat.pos_of_ne_zero (prime_product_nonzero S primes)
  have m1:62208≤M₀:=by dsimp only [M₀];nlinarith only [Nat.one_le_pow 2 _ pS]
  have pos:0<M₀:=by omega
  have cap:data.N≤M₀:=Nat.le_of_dvd pos (supported_conductor an supp ix iy eq data)
  have mono:=bound_mono data.pos cap
  unfold heightBound at mono
  have hh:=j_height_conductor data
  have jbound:logHeight₁ (jRatio W)≤(9/2)*M*(Real.log M)^2+238:=by
    dsimp only [M];linarith only [mono,hh]
  have ar:(a:ℚ)≠0:=by exact_mod_cast an
  have lx:x^3= -(jRatio W/1728)*(a:ℚ):=by rw [show jRatio W= _ from J];field_simp
  have ly:y^2=(1-jRatio W/1728)*(a:ℚ):=by rw [eq,lx];ring
  have hd:=height_div (jRatio W) 1728
  have hmul:=logHeight₁_mul_le (-(jRatio W/1728)) (a:ℚ)
  have ymul:=logHeight₁_mul_le (1-jRatio W/1728) (a:ℚ)
  have add:=logHeight₁_add_le (1:ℚ) (-(jRatio W/1728))
  have wt:(totalWeight ℚ:ℝ)=1:=by rw [NumberField.totalWeight_eq_finrank];simp
  rw [←lx,logHeight₁_pow,logHeight₁_neg,int_height an] at hmul
  rw [←ly,logHeight₁_pow,int_height an] at ymul
  rw [logHeight₁_one,logHeight₁_neg,wt,one_mul] at add
  rw [sub_eq_add_neg] at ymul
  have hc:logHeight₁ (1728:ℚ)≤11:=by
    rw [Rat.logHeight₁_eq_log_max];norm_num
    have c:=Real.log_le_log (by norm_num:(0:ℝ)<1728) (show (1728:ℝ)≤2^11 by norm_num)
    rw [Real.log_pow] at c;norm_num at c
    linarith only [c,Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)]
  have big:(62208:ℝ)≤M:=by change (62208:ℝ)≤(M₀:ℝ);exact_mod_cast m1
  have log_one:1≤Real.log M:=by
    rw [Real.le_log_iff_exp_le (by linarith only [big])]
    exact Real.exp_one_lt_d9.le.trans (by linarith only [big])
  have square:1≤(Real.log M)^2:=one_le_pow₀ log_one
  have mass:62208≤M*(Real.log M)^2:=by linarith only [mul_le_mul big square (by norm_num:(0:ℝ)≤1) (by linarith only [big]:0≤M)]
  have nonneg:=Real.log_nonneg (by exact_mod_cast Int.natAbs_pos.mpr an : (1:ℝ)≤a.natAbs)
  have mdef:M=62208*(primeProduct S:ℝ)^2:=by dsimp [M,M₀];push_cast;rfl
  rw [←mdef,ZInQ.Mult.ratHeight_eq_logHeight₁,ZInQ.Mult.ratHeight_eq_logHeight₁]
  unfold Sun28.HeightFibres.numberLog at hmul ymul
  push_cast at hmul ymul
  constructor <;> linarith only [hmul,ymul,add,hd,hc,jbound,mass,nonneg,
    Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)]

end
end Sun28.HeightCubics.Refinement
#print axioms Sun28.HeightCubics.Refinement.supported_coordinates
