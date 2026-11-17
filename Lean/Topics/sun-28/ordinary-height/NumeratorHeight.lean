import HeightConsequences

namespace Sun28.Ordinary
open Height

/-- Translating a reduced rational by an integer leaves its denominator intact. -/
theorem translated_numerator (β : ℚ) (n : ℤ) :
    (β-n).num=β.num-n*(β.den:ℤ) := by
  have calcNum (q : ℚ) : (q.num:ℚ)=q*q.den :=
    (eq_div_iff (by exact_mod_cast q.den_nz : (q.den:ℚ)≠0)).mp (Rat.num_div_den q).symm |>.symm
  have eqn : ((β-n).num:ℚ)=(β.num:ℚ)-(n:ℚ)*β.den := by
    rw [calcNum (β-n),Rat.sub_intCast_den,calcNum β]
    ring
  exact_mod_cast eqn

/-- Sun's reduced numerator is at most twice the index bound times the multiplicative height. -/
theorem numerator_le (β : ℚ) (n : ℤ) {B : ℝ} (b1 : 1≤B) (bn : |(n:ℝ)|≤B) :
    ((β-n).num.natAbs:ℝ)≤2*B*mulHeight₁ β := by
  let H := mulHeight₁ β
  have den : (β.den:ℝ)≤H := by
    rw [show H=mulHeight₁ β from rfl,Rat.mulHeight₁_eq_max]
    exact_mod_cast (le_max_right β.num.natAbs β.den)
  have num : |(β.num:ℝ)|≤H := by
    rw [show H=mulHeight₁ β from rfl,Rat.mulHeight₁_eq_max,←Int.cast_abs,←Nat.cast_natAbs]
    exact_mod_cast (le_max_left β.num.natAbs β.den)
  have hpos : 0≤H := by linarith [show 0≤(β.den:ℝ) by positivity]
  rw [translated_numerator,Nat.cast_natAbs,Int.cast_abs,Int.cast_sub,Int.cast_mul,Int.cast_natCast]
  refine (show |(β.num:ℝ)-(n:ℝ)*β.den| ≤ |(β.num:ℝ)|+|(n:ℝ)*β.den| by
    simpa only [sub_eq_add_neg,abs_neg] using (abs_add_le (β.num:ℝ) (-((n:ℝ)*β.den)))).trans ?_
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤(β.den:ℝ))]
  change _≤2*B*H
  have a : H≤B*H := by simpa using mul_le_mul_of_nonneg_right b1 hpos
  have b := mul_le_mul bn den (by positivity : 0≤(β.den:ℝ)) (by linarith : 0≤B)
  linarith

/-- The additive constant in section 7 after eliminating the index-dependent numerator. -/
noncomputable def numeratorConstant (D : ℝ) := Real.log (32*D^2)

theorem numeratorConstant_pos {D : ℝ} (h : 1≤D) : 0<numeratorConstant D := by
  apply Real.log_pos
  nlinarith [sq_nonneg (D-1)]

/-- Sun, Lemma 7.2, with the coefficient log(32 D²). -/
theorem ordinary_log_height (β : ℚ) (n : ℤ) {B D : ℝ}
    (b1 : 1≤B) (bn : |(n:ℝ)|≤B) (dp : 1≤D) (nz : β≠(n:ℚ))
    (bound : B^2≤D*(1+((β-n).num.natAbs:ℝ)^(3/2:ℝ))) :
    Real.log B≤numeratorConstant D+3*logHeight₁ β := by
  let J : ℝ := (β-n).num.natAbs
  let H := mulHeight₁ β
  have js : (β-n).num≠0 := by simpa using (sub_ne_zero.mpr nz : β-(n:ℚ)≠0)
  have jnat : 1≤(β-n).num.natAbs := Int.natAbs_pos.mpr js
  have j1 : (1:ℝ)≤J := by
    dsimp [J]
    exact_mod_cast jnat
  have J0 : 0≤J := by linarith
  have jpow := Real.one_le_rpow j1 (by norm_num : (0:ℝ)≤3/2)
  have b0 : 0<B := by linarith
  have D0 : 0<D := by linarith
  have H0 : 0<H := mulHeight₁_pos β
  have hJ : J≤2*B*H := numerator_le β n b1 bn
  have scaled : B^2 ≤ 2*D*J^(3/2:ℝ) := by
    change B^2≤D*(1+J^(3/2:ℝ)) at bound
    linarith [mul_le_mul_of_nonneg_left jpow D0.le]
  have sq := pow_le_pow_left₀ (sq_nonneg B) scaled 2
  have cancel : (J^(3/2:ℝ))^2=J^3 := by
    rw [←Real.rpow_natCast (J^(3/2:ℝ)) 2,←Real.rpow_mul J0]
    norm_num
  rw [mul_pow,cancel] at sq
  have cube := pow_le_pow_left₀ J0 hJ 3
  have B4 : B^3*B ≤ B^3*(32*D^2*H^3) := by
    have e := mul_le_mul_of_nonneg_left cube (sq_nonneg (2*D))
    linarith only [sq,e]
  have BH := (mul_le_mul_iff_right₀ (by positivity : 0<B^3)).mp B4
  have logs := Real.log_le_log b0 BH
  rw [Real.log_mul (by positivity : 32*D^2≠0) (by positivity : H^3≠0),Real.log_pow] at logs
  simpa [numeratorConstant,H,logHeight₁_eq_log_mulHeight₁] using logs

end Sun28.Ordinary
#print axioms Sun28.Ordinary.translated_numerator
#print axioms Sun28.Ordinary.numerator_le
#print axioms Sun28.Ordinary.numeratorConstant_pos
#print axioms Sun28.Ordinary.ordinary_log_height
