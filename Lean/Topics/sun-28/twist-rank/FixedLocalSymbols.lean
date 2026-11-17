import PoleImage
import RationalPrimeOutput

namespace Sun28.TwistRank
open PreparedPoles PairedClasses FixedPreparation

/-- The actual fixed-prime restrictions exclude admissible pairs. The old
rational conic example supplies one such pair even with both twist points. -/
theorem excluded_admissible : AdmissiblePair 17 3697 ∧ NormConic 17 3697 ∧ ¬FixedSquares 3697 := by
  refine ⟨TwistPrimes.rational_prime_example.2.1,?_,?_⟩
  · exact ⟨4/63,1/63,by norm_num,by norm_num,by norm_num⟩
  · intro fixed
    have roots := (fixed 5 (by decide) (by decide) (by decide)).2
    obtain ⟨t,h⟩ := roots 1
    have m : t^2 ≡ 3697 [ZMOD 5] := by simpa using h
    have z := (ZMod.intCast_eq_intCast_iff _ _ 5).mpr m
    push_cast at z
    exact (show ∀ x : ZMod 5, x^2≠3697 by decide) _ z

/-- Further geometric information at the chosen point of the norm conic
discharges the pole for a prescribed pair with n=β. -/
theorem fixed_first_twist {β θ : ℕ} (hb : 0 < β) {u v w : ℚ} (uv : v≠0)
    (conic : (β:ℚ)*u^2+θ*v^2=1)
    (extra : w^2=1+3*(β:ℚ)*u^2) : TwistPoint β (β*θ) := by
  have bp : (0:ℚ) < β := by exact_mod_cast hb
  have wn : w≠0 := by
    intro z
    rw [z,zero_pow (by decide : 2≠0)] at extra
    nlinarith [mul_nonneg bp.le (sq_nonneg u)]
  have cn : (θ:ℚ)*v^2=1-(β:ℚ)*u^2 := by linarith
  have dif : (β:ℚ)*(w/v)^2-β*θ=(2*(β:ℚ)*u/v)^2 := by
    field_simp
    linear_combination extra-conic
  have plus : (β:ℚ)*(w/v)^2+3*(β:ℚ)*θ=(β:ℚ)*(2/v)^2 := by
    field_simp
    linear_combination extra+3*conic
  refine ⟨w/v,4*(β:ℚ)^2*u*w/v^3,div_ne_zero wn uv,?_⟩
  dsimp only
  push_cast
  rw [dif,show (β:ℚ)*(w/v)^2+3*((β:ℚ)*θ)=β*(2/v)^2 by linarith [plus]]
  ring

/-- The other square condition on the same conic gives a second
explicit section, also with twist parameter n=β. -/
theorem fixed_first_twist_other {β θ : ℕ} (hb : 0<β) {u v w : ℚ} (uv : v≠0)
    (conic : (β:ℚ)*u^2+θ*v^2=1)
    (extra : w^2=1+3*(θ:ℚ)*v^2) : TwistPoint β (β*θ) := by
  have bp : (0:ℚ)<β := by exact_mod_cast hb
  have dif : (β:ℚ)*(1/v)^2-β*θ=(β*u/v)^2 := by
    field_simp
    linear_combination -conic
  have plus : (β:ℚ)*(1/v)^2+3*(β:ℚ)*θ=(β:ℚ)*(w/v)^2 := by
    field_simp
    linear_combination -extra
  refine ⟨1/v,(β:ℚ)^2*u*w/v^3,div_ne_zero one_ne_zero uv,?_⟩
  dsimp only
  push_cast
  rw [dif,show (β:ℚ)*(1/v)^2+3*((β:ℚ)*θ)=β*(w/v)^2 by linarith [plus]]
  ring

def SquareSection (β θ : ℕ) : Prop := ∃ u v w : ℚ, u≠0 ∧ v≠0 ∧
    (β:ℚ)*u^2+θ*v^2=1 ∧ (w^2=1+3*(β:ℚ)*u^2 ∨ w^2=1+3*(θ:ℚ)*v^2)

theorem realized_of_section {β θ : ℕ} (hb : 0<β) (hs : Squarefree β) (cop : β.Coprime (6*θ))
    (s : SquareSection β θ) : Realized β θ := by
  obtain ⟨u,v,w,_,nz,c,extra⟩:=s
  refine ⟨β,hb,hs,cop,⟨1,0,one_ne_zero,by norm_num⟩,?_⟩
  exact extra.elim (fixed_first_twist hb nz c) (fixed_first_twist_other hb nz c)

end Sun28.TwistRank
#print axioms Sun28.TwistRank.excluded_admissible
#print axioms Sun28.TwistRank.fixed_first_twist

#print axioms Sun28.TwistRank.fixed_first_twist_other
#print axioms Sun28.TwistRank.realized_of_section

