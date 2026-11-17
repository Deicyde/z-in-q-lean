import FiniteCharts

namespace Sun28.ConicCovers
open Sun28.FactorHeights
noncomputable section

def ratSquare (z : ℚ) : Prop := ∃ y : ℚ, z=y^2

/-- The first coordinate is the ratio of the two previously marked ordinates. -/
theorem positive_lines {x : ℚ} (hc : conics x 2 1 1) :
    ∃ t : ℚ, |t|<1 ∧ ratSquare (2*(1-t^2)) ∧
      ratSquare (14*(225-t^2)) ∧ ratSquare (3*t^2+2398) ∧ 3*t^2+2398=2401*(x^2/(x^2+3/2)) := by
  obtain ⟨u,v,w,hu,_hv,_hw,eu,ev,ew⟩:=hc
  norm_num at eu ev ew
  have h: x^2+3/2=u^2 :=by linarith
  have d: u^2-v^2=2401/2 := by linarith
  have w2: w^2=14*(225*u^2-v^2)/49 := by linarith
  refine ⟨v/u,?_,⟨49/u,?_⟩,⟨7*w/u,?_⟩,⟨49*x/u,?_⟩,?_⟩
  · rw [abs_div,div_lt_one (abs_pos.mpr hu)]
    exact (sq_lt_sq.mp (by nlinarith only [d] : v^2<u^2))
  · field_simp; linarith
  · field_simp; linarith
  · field_simp;linarith
  · rw [h];field_simp;linarith

/-- On the second branch the ratio is the positive ordinate divided by 7. -/
theorem negative_lines {x : ℚ} (hc : conics x 14 (-35) 7) :
    ∃ t : ℚ, 1<t ∧ t<15 ∧ ratSquare (t^2-1) ∧
       ratSquare (5*(225-t^2)) ∧ 343*t^2-439=(8*x)^2 := by
  obtain ⟨u,v,w,hu,hv,_hw,eu,ev,ew⟩:=hc
  norm_num at eu ev ew
  have E1:w^2-49=(8*u)^2 := by linarith
  have E2:11025-w^2=5*(8*v)^2 := by linarith
  have hr: |w|^2=w^2 := sq_abs _
  have pos:=abs_nonneg w
  have s1:=sq_pos_of_ne_zero hu
  have s2:=sq_pos_of_ne_zero hv
  refine ⟨|w|/7,?_,?_,⟨8*u/7,?_⟩,⟨40*v/7,?_⟩,?_⟩ <;> nlinarith

end
end Sun28.ConicCovers
#print axioms Sun28.ConicCovers.positive_lines
#print axioms Sun28.ConicCovers.negative_lines
