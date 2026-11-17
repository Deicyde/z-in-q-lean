import IntegerGap
import PrimitiveCircle
import PencilRowContact

namespace Sun28.PointPencils
open Height Sun28.ScalarHeight Sun28.ScalarLucas
noncomputable section

theorem centre_height (x : ℚ) {d w : ℕ} {u v p c : ℤ} (h : Circle x d w u v p c) :
    logHeight₁ (beta x)≤Real.log (circleCap x d p c) := by
  let g:ℤ:=reduction x
  let A:ℤ:=(beta x).num
  let B:ℤ:=(beta x).den
  obtain ⟨pos,an,height,num⟩:=beta_num_facts x
  change 0<g at pos
  change 0<A at an
  change logHeight₁ (beta x)=Real.log (A:ℝ) at height
  change g*A≤3*(x.num^2+(x.den:ℤ)^2) at num
  have norm : x.num^2+(x.den:ℤ)^2=(d:ℤ)*(w:ℤ)^2 := by
    rw [h.point.1,h.point.2,←h.seed,←h.equation]
    ring
  have gap:=primitive_gap h.primitive h.equation
  have gg:=mul_self_le_mul_self (show 0≤2*(w:ℤ) by positivity) gap
  have scaled: 4*(g*A)≤3*(d:ℤ)*(gapSize p c)^2 := by
    have grow:=mul_le_mul_of_nonneg_left gg (show 0≤3*(d:ℤ) by positivity)
    calc
      4*(g*A) ≤ 12*(x.num^2+(x.den:ℤ)^2) := by linarith only [num]
      _ = 12*((d:ℤ)*(w:ℤ)^2) := by rw [norm]
      _ ≤ _ := by convert grow using 1 <;> ring
  rw [height]
  apply Real.log_le_log (by exact_mod_cast an)
  unfold circleCap
  have gp : 0<((reduction x:ℕ):ℝ) := Nat.cast_pos.mpr (Nat.gcd_pos_of_pos_left _ (by decide:0<2))
  apply (le_div_iff₀ (mul_pos (by norm_num : 0<(4:ℝ)) gp)).mpr
  change (A:ℝ)*(4*(g:ℝ))≤_
  exact_mod_cast (show A*(4*g)≤3*(d:ℤ)*(gapSize p c)^2 by linarith only [scaled])

def CentreTest (x : ℚ) : Prop :=
  ∃ (d w : ℕ) (u v p c : ℤ), Circle x d w u v p c ∧
    Real.log (circleCap x d p c) ≤ scalarAllowance x

theorem of_centre_test (x : ℚ) (test : CentreTest x) : logHeight₁ (beta x) ≤ scalarAllowance x := by
  obtain ⟨d,w,u,v,p,c,actual,fit⟩:=test
  exact (centre_height x actual).trans fit

end
end Sun28.PointPencils
#print axioms Sun28.PointPencils.centre_height
#print axioms Sun28.PointPencils.of_centre_test
