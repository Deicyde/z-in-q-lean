import CertificateHeights

/-! The height comparison after the Lucas discrepancy has vanished. -/
namespace Sun28.IndexHeights
open Sun28.Ordinary Sun28.FixedPreparation Height
noncomputable section

theorem numerator_bound (β : ℚ) (n : ℤ) :
    ((β-n).num.natAbs:ℝ)≤(1+|(n:ℝ)|)*mulHeight₁ β := by
  let H:=mulHeight₁ β
  have den : (β.den:ℝ)≤H := by
    rw [show H=mulHeight₁ β from rfl,Rat.mulHeight₁_eq_max]
    exact_mod_cast le_max_right β.num.natAbs β.den
  have num : |(β.num:ℝ)|≤H := by
    rw [show H=mulHeight₁ β from rfl,Rat.mulHeight₁_eq_max,←Int.cast_abs,←Nat.cast_natAbs]
    exact_mod_cast le_max_left β.num.natAbs β.den
  rw [translated_numerator,Nat.cast_natAbs,Int.cast_abs,Int.cast_sub,Int.cast_mul,Int.cast_natCast]
  calc
    _ ≤ |(β.num:ℝ)|+|((n:ℝ)*β.den)| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (β.num:ℝ) (-(n*β.den:ℝ))
    _ ≤ H+|(n:ℝ)| *H := by rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤β.den)];gcongr
    _ = _ := by dsimp [H];ring

/-- Only the two indicated multiples of the generator occur. -/
def NumeratorTest (n : Fin 4 → ℤ) (U:ℕ) : Prop :=
  (1+|(n 0:ℝ)|)^3*|(n 2:ℝ)| ≤ 32*ordinary^2*(U:ℝ)^48

theorem numerator_log (n : Fin 4 → ℤ) (β:ℚ) {U : ℕ} (noninteger : β≠(n 0:ℚ))
    (live : n 2 ≠ 0) (divides : U^16 ∣ (β-n 0).num.natAbs) (test : NumeratorTest n U) :
    Real.log |(n 2:ℝ)| ≤ logConstant+3*logHeight₁ β := by
  have nJ : 0<(β-n 0).num.natAbs:=Int.natAbs_pos.mpr ((Rat.num_ne_zero).mpr (sub_ne_zero.mpr noninteger))
  have bound : (U:ℝ)^16 ≤ ((β-n 0).num.natAbs:ℝ) := by exact_mod_cast Nat.le_of_dvd nJ divides
  have cube:=pow_le_pow_left₀ (by positivity : 0≤(U:ℝ)^16) (bound.trans (numerator_bound β (n 0))) 3
  rw [←pow_mul,mul_pow] at cube
  have mul := mul_le_mul_of_nonneg_left cube (by positivity : (0:ℝ)≤32*ordinary^2)
  have pos : 0<(1+|(n 0:ℝ)|)^3 := by positivity
  have final : |(n 2:ℝ)|≤32*ordinary^2*(mulHeight₁ β)^3 := by
    apply (mul_le_mul_iff_right₀ pos).mp
    unfold NumeratorTest at test
    calc
      _ ≤ 32*ordinary^2*(U:ℝ)^48 := test
      _ ≤ _ := by
        calc
          _ ≤ 32*ordinary^2*((1+|(n 0:ℝ)|)^3*mulHeight₁ β^3) := mul
          _ = _ := by ring
  have op : 0<ordinary := by unfold ordinary glazerConstant24; positivity
  have Hpos :=mulHeight₁_pos β
  have logs:=Real.log_le_log (abs_pos.mpr (by exact_mod_cast live : (n 2:ℝ)≠0)) final
  rw [Real.log_mul (by positivity : (32:ℝ)*ordinary^2≠0) (pow_ne_zero 3 Hpos.ne'),Real.log_pow] at logs
  simpa only [logConstant,Nat.cast_ofNat,logHeight₁_eq_log_mulHeight₁] using logs

end
end Sun28.IndexHeights
#print axioms Sun28.IndexHeights.numerator_bound
#print axioms Sun28.IndexHeights.numerator_log
