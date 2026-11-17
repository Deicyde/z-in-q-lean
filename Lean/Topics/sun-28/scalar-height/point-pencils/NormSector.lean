import CentreBudget
import UnitNumerator

namespace Sun28.PointPencils
open Height Sun28.ScalarHeight Sun28.ScalarLucas Sun28.WitnessHeight Sun28.FiveMarkUnits
open Sun28.HeightFibres Sun28.ScalarPencil
noncomputable section
set_option exponentiation.threshold 1200

theorem class_bound (x : ℚ) : (scalarClass x).natAbs≤totalRadical x := by
  have sf:=Int.squarefree_natAbs.mpr (octic_twist x).1
  have old:=FiveDescent.fixed_cost (scalarClass x) 1
  rw [totalRadical_eq]
  simpa only [FiveDescent.parameterPrimes,FiveDescent.twistPrimes,scalarPrimes,Int.natAbs_one,
    Nat.primeFactors_one,Finset.union_empty,primeProduct,Nat.prod_primeFactors_of_squarefree sf] using old

private theorem radical_fits (x : ℚ) (H : ℝ) (h : H≤90*(totalRadical x:ℝ)) :
    H ≤ scalarAllowance x := by
  have pos : (1:ℝ)≤totalRadical x:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd _ _))
  have grow:=pow_le_pow_right₀ pos (by decide : 1≤24)
  rw [pow_one] at grow
  have coeff : (90:ℝ)≤2^810 := by norm_num
  have cmp:=h.trans (mul_le_mul coeff grow (by positivity) (by positivity))
  have eq:oddProduct (beta x).num (beta x).den=radical x:=by
    unfold oddProduct oddSupport radical;rw [scalar_support_exact]
  exact cmp.trans ((eq ▸ original_margin (beta x).num (beta x).den).trans (original_fits x))

/-- A large prime in the norm to the first power is charged through the
actual octic radical. Only the square factor w costs a logarithm. -/
theorem norm_height (x : ℚ) {d w : ℕ} {u v p c : ℤ} (h : Circle x d w u v p c) :
    logHeight₁ (beta x)≤Real.log (3*(d:ℝ))+2*Real.log (w:ℝ) := by
  let norm : ℤ:=x.num^2+(x.den:ℤ)^2
  have eq : norm=(d:ℤ)*(w:ℤ)^2 := by
    dsimp [norm];rw [h.point.1,h.point.2,←h.seed,←h.equation];ring
  let A:ℤ:=(beta x).num
  let g:ℤ:=reduction x
  obtain ⟨gp,an,height,num⟩:=beta_num_facts x
  change 0<g at gp
  change 0<A at an
  change logHeight₁ (beta x)=Real.log (A:ℝ) at height
  change g*A≤3*norm at num
  have aN:A≤3*((d:ℤ)*(w:ℤ)^2) := by
    rw [←eq]
    exact (le_mul_of_one_le_left an.le gp).trans num
  have dp : 0<(d:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h.squarefree.ne_zero
  have wp : 0<(w:ℝ):=by exact_mod_cast h.positive
  have ap : (A:ℝ)≤(3*(d:ℝ))*(w:ℝ)^2 := by exact_mod_cast (show A≤(3*(d:ℤ))*(w:ℤ)^2 by rwa [mul_assoc])
  have cmp:=Real.log_le_log (show 0<(A:ℝ) by exact_mod_cast an) ap
  rw [Real.log_mul (by positivity : 3*(d:ℝ)≠0) (pow_ne_zero 2 wp.ne'),Real.log_pow] at cmp
  rw [height]
  exact cmp

/-- No assumption on any other factor or on the separate numerator or denominator. -/
theorem squarefree_norm (x : ℚ) (sf : Squarefree (x.num.natAbs^2+x.den^2)) :
    logHeight₁ (beta x) ≤ scalarAllowance x := by
  obtain ⟨d,w,u,v,p,c,h⟩:=realized_circle x
  have norm : x.num.natAbs^2+x.den^2=w^2*d := by
    have z : (x.num.natAbs:ℤ)^2+(x.den:ℤ)^2=(w:ℤ)^2*d := by
      rw [Int.natCast_natAbs,sq_abs,h.point.1,h.point.2,←h.seed,←h.equation];ring
    exact_mod_cast z
  have unit := sf w (by rw [←sq,norm];exact dvd_mul_right ..)
  have one:=Nat.isUnit_iff.mp unit
  have hh:=norm_height x h
  rw [one,Nat.cast_one,Real.log_one,mul_zero,add_zero] at hh
  have dsmall:=Nat.le_of_dvd (Nat.mul_pos (by decide) (Int.natAbs_pos.mpr (octic_twist x).1.ne_zero)) h.octicSupport
  have bound:d≤30*totalRadical x:=dsmall.trans (Nat.mul_le_mul_left _ (class_bound x))
  have bound' : (d:ℝ)≤30*(totalRadical x:ℝ):=by exact_mod_cast bound
  have dp : 0<(d:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero h.squarefree.ne_zero
  apply radical_fits
  linarith only [hh,Real.log_le_sub_one_of_pos (show 0<3*(d:ℝ) by positivity),bound']

/-- The logarithm of the short normalized leg may grow like the 24th
power of the complete odd radial product. -/
theorem short_leg_sector (x : ℚ) {d w : ℕ} {u v p c : ℤ} (h : Circle x d w u v p c)
    (small : Real.log ((gapSize p c:ℤ):ℝ) ≤ (totalRadical x:ℝ)^24) :
    logHeight₁ (beta x) ≤ scalarAllowance x := by
  let T:ℝ:=totalRadical x
  have T1 : 1≤T:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd _ _))
  have grow:=pow_le_pow_right₀ T1 (by decide:1≤24)
  rw [pow_one] at grow
  have extra:=Nat.le_of_dvd (Nat.mul_pos (by decide) (Int.natAbs_pos.mpr (octic_twist x).1.ne_zero)) h.octicSupport
  have de:d≤30*totalRadical x:=extra.trans (Nat.mul_le_mul_left _ (class_bound x))
  have ds:(d:ℝ)≤30*T:=by dsimp only [T];exact_mod_cast de
  have dp:0<(d:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero h.squarefree.ne_zero
  have gt:0<(gapSize p c:ℝ):=by
    have lower:(2:ℤ)≤gapSize p c:=le_max_left .. 
    exact_mod_cast (lt_of_lt_of_le (by decide : (0:ℤ)<2) lower)
  have gp:1≤(reduction x:ℝ):=Nat.one_le_cast.mpr (Nat.gcd_pos_of_pos_left _ (by decide:0<2))
  have numPos:0<3*(d:ℝ)*(gapSize p c:ℝ)^2:=by positivity
  have cc:circleCap x d p c≤3*(d:ℝ)*(gapSize p c:ℝ)^2:=by
    unfold circleCap
    exact div_le_self numPos.le (by linarith only [gp])
  have cp:0<circleCap x d p c:= by
    unfold circleCap
    exact div_pos numPos (by linarith only [gp])
  have hh:=(centre_height x h).trans (Real.log_le_log cp cc)
  rw [Real.log_mul (by positivity:3*(d:ℝ)≠0) (pow_ne_zero 2 gt.ne'),Real.log_pow] at hh
  have logd:=Real.log_le_sub_one_of_pos (show 0<3*(d:ℝ) by positivity)
  change Real.log (gapSize p c:ℝ) ≤ T^24 at small
  have sm:logHeight₁ (beta x)≤92*T^24 := by
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh,logd,ds,grow,small]
  have constant : (92:ℝ)≤2^810 := by norm_num
  have le:=sm.trans (mul_le_mul_of_nonneg_right constant (by positivity))
  have eq:oddProduct (beta x).num (beta x).den=radical x:=by
    unfold oddProduct oddSupport radical;rw [scalar_support_exact]
  exact le.trans ((eq ▸ original_margin (beta x).num (beta x).den).trans (original_fits x))

end
end Sun28.PointPencils
#print axioms Sun28.PointPencils.class_bound
#print axioms Sun28.PointPencils.norm_height
#print axioms Sun28.PointPencils.squarefree_norm
#print axioms Sun28.PointPencils.short_leg_sector
