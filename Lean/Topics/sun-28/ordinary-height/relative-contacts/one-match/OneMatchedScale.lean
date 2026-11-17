import OrdinaryDivisors

namespace Sun28.RelativeContacts
open ZInQ ZInQ.Mult Sun28.Ordinary Sun28.Forward Sun28.ScalarHeight Sun28.WitnessIndices
open Sun28.FixedPreparation Sun28.WitnessHeight Sun28.IndexHeights Height
noncomputable section
set_option maxRecDepth 12000

/-- A rational number of absolute value at most the archimedean bound a
costs at most the height of a and its own reduced denominator. -/
theorem height_of_archimedean_bound {a b : ℚ} (bound : |(b:ℝ)|≤(a:ℝ)) :
    logHeight₁ b≤logHeight₁ a+Real.log (b.den:ℝ) := by
  let M:ℕ:=max a.num.natAbs a.den
  have one:1≤M:=a.den_pos.trans_le (le_max_right ..)
  have num (z:ℚ) : (z:ℝ)*(z.den:ℝ)=(z.num:ℝ) := by
    exact_mod_cast (eq_div_iff (by exact_mod_cast z.den_nz : (z.den:ℚ)≠0)).mp z.num_div_den.symm
  have absnum (z:ℚ) : (z.num.natAbs:ℝ)=|(z:ℝ)| *(z.den:ℝ) := by
    rw [Nat.cast_natAbs,Int.cast_abs,←num z,abs_mul,abs_of_nonneg (show (0:ℝ)≤z.den from Nat.cast_nonneg _)]
  have wide : (a:ℝ)≤M := by
    have up : (a.num.natAbs:ℝ)≤M := by exact_mod_cast (le_max_left a.num.natAbs a.den)
    rw [absnum] at up
    have de : (1:ℝ)≤a.den:=by exact_mod_cast a.den_pos
    exact (le_abs_self _).trans ((le_mul_of_one_le_right (abs_nonneg _) de).trans up)
  have n : (b.num.natAbs:ℝ)≤M*(b.den:ℝ) := by
    rw [absnum]
    exact mul_le_mul_of_nonneg_right (bound.trans wide) (Nat.cast_nonneg _)
  have d : (b.den:ℝ)≤M*(b.den:ℝ) := le_mul_of_one_le_left (Nat.cast_nonneg _) (by exact_mod_cast one)
  have total : ((max b.num.natAbs b.den:ℕ):ℝ)≤(M:ℝ)*b.den := by
    rw [Nat.cast_max]; exact max_le n d
  have live:0 < max b.num.natAbs b.den:=b.den_pos.trans_le (le_max_right ..)
  have lg:=Real.log_le_log (by exact_mod_cast live : (0:ℝ)<(max b.num.natAbs b.den:ℕ)) total
  rw [Real.log_mul (by positivity : (M:ℝ)≠0) (by exact_mod_cast b.den_nz)] at lg
  simpa only [Rat.logHeight₁_eq_log_max,M] using lg

theorem product_archimedean (A : Fin 9→AffineInput) (x η : ℚ)
    (accepted : PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers) :
    let C:=rootProduct (nineAffine A).doubles fixedMultiplier
    |(C.im:ℝ)|≤C.re := by
  let C:=rootProduct (nineAffine A).doubles fixedMultiplier
  change |(C.im:ℝ)|≤C.re
  have o : 0≤ordinary:=by unfold ordinary glazerConstant24;positivity
  have g : 0≤glazerConstant24:=by unfold glazerConstant24;positivity
  obtain ⟨a,e,_⟩:=extract_indices A anchor (K:=logConstant) o g
    accepted.q_nonzero accepted.h_nonzero accepted.base_nonzero accepted.odd_N accepted.odd_T accepted.odd_Z
  have coords : coordinateProduct a.n=C := rootProduct_eq e.represented
  have positive (σ : K0 →+*ℝ) (hδ:1≤σ delta) : 1≤σ C := by
    rw [←coords,coordinateProduct,map_prod]
    have lo (i:Fin 4) : 1≤σ (indexX (a.n i)) := by
      have ni : a.n i≠0:=by obtain ⟨k,hk⟩:=e.odd i; omega
      exact hδ.trans (generator_real_lower σ hδ ni)
    rw [Fin.prod_univ_four]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (lo 0) (lo 1)) (lo 2)) (lo 3)
  have p:=positive K0.embPlus embPlus_delta_mem.1
  have m:=positive K0.embMinus embMinus_delta_mem.1
  rw [K0.embPlus_apply] at p
  rw [K0.embMinus_apply] at m
  have s : 1≤Real.sqrt 2 := by
    have h:=Real.sq_sqrt (show 0≤(2:ℝ) by norm_num)
    nlinarith [Real.sqrt_nonneg (2:ℝ)]
  rw [abs_le]
  by_cases h:0≤(C.im:ℝ)
  · have grow:=mul_nonneg h (sub_nonneg.mpr s)
    constructor <;> nlinarith only [p,m,grow,h]
  · have h0 := le_of_not_ge h
    have grow:=mul_nonneg (neg_nonneg.mpr h0) (sub_nonneg.mpr s)
    constructor <;> nlinarith only [p,m,grow,h0]

def singleBudget (C:K0) (η:ℚ) : ℝ :=
  Real.log 3905573+2*Real.log ((η.den:ℝ)*C.re.den^2)+Real.log C.im.den+11

theorem indices_of_one_match (A : Fin 9→AffineInput) (x η : ℚ)
    (accepted : PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers)
    (one:Matched (pointScale (nineAffine A).doubles fixedMultiplier 1) η)
    (budget:singleBudget (rootProduct (nineAffine A).doubles fixedMultiplier) η≤
      ordinary*(unionRadical oldCutoff (slope (nineAffine A).doubles η):ℝ)^24) :
    OrdinaryIndices A η := by
  let C:=rootProduct (nineAffine A).doubles fixedMultiplier
  have en : η≠0 := by
    rintro rfl
    have bad := (accepted.scale_guard 0).1
    rw [mul_zero] at bad
    exact bad (by simp [marks])
  have arch:=product_archimedean A x η accepted
  change |(C.im:ℝ)|≤C.re at arch
  have cost:=height_of_archimedean_bound arch
  have oneCost:=matched_height en one
  change 2*logHeight₁ C.re≤Real.log 3905573+2*Real.log ((η.den:ℝ)*C.re.den^2) at oneCost
  have add:=logHeight₁_add_le (1:ℚ) (C.im^2)
  have wt : (totalWeight ℚ:ℝ)=1 := by rw [NumberField.totalWeight_eq_finrank];simp
  rw [wt,one_mul,logHeight₁_one,add_zero,logHeight₁_pow] at add
  norm_num only [Nat.cast_ofNat] at add
  apply of_ratios A x η accepted
  apply le_trans _ budget
  change ratioHeight (fun i=>(scaleRoot C.re C.im i)^2*η)+10 ≤ singleBudget C η
  have z : (scaleRoot C.re C.im 0)^2*η=η := by simp [scaleRoot]
  have a : (scaleRoot C.re C.im 1)^2*η/η=C.re^2 := by simp [scaleRoot,en]
  have b : (scaleRoot C.re C.im 2)^2*η/η=(1+C.im^2)^2 := by simp [scaleRoot,en]
  simp only [ratioHeight,z,a,b,logHeight₁_pow,Nat.cast_ofNat,singleBudget]
  linarith only [cost,oneCost,add,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

end
end Sun28.RelativeContacts
#print axioms Sun28.RelativeContacts.height_of_archimedean_bound
#print axioms Sun28.RelativeContacts.product_archimedean
#print axioms Sun28.RelativeContacts.indices_of_one_match

