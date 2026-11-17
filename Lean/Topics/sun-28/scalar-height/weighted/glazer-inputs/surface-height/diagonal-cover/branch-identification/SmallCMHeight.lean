import CMPeriod

namespace ZInQBlueprint.BranchId
open CMPeriods
noncomputable section

/-- The coarse CM order test supplies the bound on the actual reduced forms. -/
theorem reduced_period_small {d : ℕ} {z : ℂ} (P : ReducedPeriod d z)
    (bound : d ≤ 5460) : 1/2 ≤ z.im ∧ z.im ≤ 37 := by
  let a : ℝ := P.a
  let b : ℝ := P.b
  let c : ℝ := P.c
  have ap : (1:ℝ)≤a := by dsimp [a]; exact_mod_cast (show 1≤P.a from P.positive)
  have ac : a≤c := by dsimp [a,c]; exact_mod_cast P.reducedC
  have bh : |b|≤a := by simpa only [b,a,Nat.cast_natAbs,Int.cast_abs] using (show (P.b.natAbs:ℝ)≤P.a by exact_mod_cast P.reducedB)
  have bb : b^2 ≤ a^2 := (sq_le_sq₀ (abs_nonneg _) (by linarith)).mpr bh |> fun h => by simpa using h
  have D : (d:ℝ) = 4*a*c-b^2 := by dsimp [a,b,c]; exact_mod_cast P.discr
  have top : (d:ℝ)≤74^2 := by exact_mod_cast (bound.trans (by decide : 5460≤74^2))
  have re := congrArg Complex.re P.root
  have im := congrArg Complex.im P.root
  simp only [pow_two,Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.add_im,
    Complex.natCast_re,Complex.natCast_im,Complex.intCast_re,Complex.intCast_im,
    Complex.zero_re,Complex.zero_im,zero_mul,add_zero,sub_zero] at re im
  change a*(z.re*z.re-z.im*z.im)+b*z.re+c=0 at re
  have im' : (2*a*z.re+b)*z.im=0 := by
    dsimp [a,b]
    linear_combination im
  have bx := (mul_eq_zero.mp im').resolve_right P.upper.ne'
  have disc : (2*a*z.im)^2=(d:ℝ) := by
    linear_combination -4*a*re + (2*a*z.re+b)*bx - D
  have low : a^2 ≤ (2*a*z.im)^2 := by
    rw [disc,D]
    nlinarith only [bb,mul_nonneg (show 0≤a by linarith) (sub_nonneg.mpr ac),sq_nonneg a]
  have ar : 0<a := by linarith
  have pos := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) ar.le) P.upper.le
  have l := (sq_le_sq₀ ar.le pos).mp low
  have u := (sq_le_sq₀ pos (by norm_num : (0:ℝ)≤74)).mp (disc.trans_le top)
  constructor
  · by_contra! hz
    nlinarith only [l,mul_pos ar (sub_pos.mpr hz)]
  · nlinarith only [u, mul_nonneg (sub_nonneg.mpr ap) P.upper.le]

theorem small_cm_height {h : ℝ} (A : PeriodPresentation h) (bound : orderDiscriminant A.fibre≤5460) : h ≤ 80 := by
  let := A.finite
  have each (σ) (i) : periodHeight (A.periods i σ) ≤ 40 := by
    have yz := reduced_period_small (A.forms i σ) bound
    exact (periodHeight_le yz.1).trans (by linarith only [yz.2])
  rw [A.faltings]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (Module.finrank_pos (R:=ℚ) (M:=A.field)))).2
  calc
    _ ≤ ∑ _σ : A.field →ₐ[ℚ] ℂ, ∑ _i : Fin 2, (40:ℝ) :=
      Finset.sum_le_sum (fun σ _ => Finset.sum_le_sum (fun i _ => each σ i))
    _ = _ := by simp [AlgHom.card]; ring
end
end ZInQBlueprint.BranchId
#print axioms ZInQBlueprint.BranchId.reduced_period_small
#print axioms ZInQBlueprint.BranchId.small_cm_height
