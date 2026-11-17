import ScalarEstimates

namespace Sun28.PointPencils
open Height Sun28.ScalarHeight
noncomputable section

def reduction (x : ℚ) : ℕ := Nat.gcd 2 (x.den^2)

/-- The reduced numerator of β realizes its multiplicative height. The division
by gcd(2,b²) accounts for the even-denominator case. -/
theorem beta_num_facts (x : ℚ) :
    let A:ℤ:=(beta x).num
    let g:ℤ:=reduction x
    0<g ∧ 0<A ∧ logHeight₁ (beta x)=Real.log (A:ℝ) ∧
      g*A≤3*(x.num^2+(x.den:ℤ)^2) := by
  let g:ℤ:=reduction x
  let A:ℤ:=(beta x).num
  let B:ℤ:=(beta x).den
  have pos : 0<g := by dsimp [g,reduction];exact_mod_cast Nat.gcd_pos_of_pos_left (x.den^2) (by decide:0<2)
  have den : B*g=(x.den:ℤ)^2 := by
    dsimp [g,reduction,B]
    exact_mod_cast WitnessHeight.scalar_denominator x
  have num : g*A=2*x.num^2+3*(x.den:ℤ)^2 := (ScalarPencil.rows x).1
  have bg : g*B≤g*A := by
    rw [num,mul_comm g B,den]
    linarith only [sq_nonneg x.num,sq_nonneg (x.den:ℤ)]
  have ab : B≤A := (mul_le_mul_iff_right₀ pos).mp bg
  have bn : 0<B := by dsimp [B];exact_mod_cast (beta x).den_pos
  have an : 0<A := bn.trans_le ab
  have aneq : (A.natAbs:ℤ)=A := (Int.natCast_natAbs A).trans (abs_of_pos an)
  have mx : max (beta x).num.natAbs (beta x).den=(beta x).num.natAbs := by
    apply max_eq_left
    change (beta x).den≤A.natAbs
    exact (Int.ofNat_le).mp (show B≤(A.natAbs:ℤ) by rw [aneq];exact ab)
  refine ⟨pos,an,?_,?_⟩
  · rw [Rat.logHeight₁_eq_log_max,mx]
    change Real.log (A.natAbs:ℝ)=Real.log (A:ℝ)
    apply congrArg Real.log
    rw [←Int.cast_natCast (R:=ℝ),aneq]
  · change g*A≤3*(x.num^2+(x.den:ℤ)^2)
    rw [num];linarith only [sq_nonneg x.num]

end
end Sun28.PointPencils
#print axioms Sun28.PointPencils.beta_num_facts
