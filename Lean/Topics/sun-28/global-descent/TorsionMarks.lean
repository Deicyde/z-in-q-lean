import GlobalSections

namespace Sun28.GlobalDescent
open Sun28.GlobalSections
noncomputable section

/-- An affine point in a nonzero x-class, allowing arbitrary field representatives. -/
def Mark (r d : ℚ) : Prop := ∃ u y : ℚ, u≠0 ∧ y≠0 ∧ equation r (d*u^2) y

theorem represented_iff (b r : ℚ) : represented b r ↔ Mark r (b*lead r) := Iff.rfl

theorem rescale {r d t : ℚ} (nz:t≠0) : Mark r d ↔ Mark r (d*t^2) := by
  constructor
  · rintro ⟨u,y,un,yn,h⟩
    refine ⟨u/t,y,div_ne_zero un nz,yn,?_⟩
    have e : d*t^2*(u/t)^2=d*u^2 := by field_simp
    simpa only [e] using h
  · rintro ⟨u,y,un,yn,h⟩
    refine ⟨t*u,y,mul_ne_zero nz un,yn,?_⟩
    simpa only [mul_pow,mul_assoc] using h

/-- Translation by (0,0) takes x to BC/x. The original ordinate is nonzero. -/
theorem translate_zero {B C x y : ℚ} (xb:x≠0) (B0:B≠0) (C0:C≠0) (hy:y≠0)
    (E:y^2=x*(x+B)*(x+C)) :
    let z:=B*C/x
    let v:= -(B*C)*y/x^2
    v≠0 ∧ v^2=z*(z+B)*(z+C) := by
  dsimp only
  refine ⟨div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero B0 C0)) hy) (pow_ne_zero 2 xb),?_⟩
  field_simp
  ring_nf at *
  assumption

/-- Translation by (-B,0). Its new abscissa is -B times (y/(x+B))²/x. -/
theorem translate_minus {B C x y : ℚ} (B0:B≠0) (sep:B≠C) (xb:x+B≠0) (hy:y≠0)
    (E:y^2=x*(x+B)*(x+C)) :
    let z:= -B*(x+C)/(x+B)
    let v:= -B*(B-C)*y/(x+B)^2
    v≠0 ∧ v^2=z*(z+B)*(z+C) ∧ x*z= -B*(y/(x+B))^2 := by
  dsimp only
  refine ⟨div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr B0) (sub_ne_zero.mpr sep)) hy)
      (pow_ne_zero 2 xb),?_,?_⟩
  · field_simp
    ring_nf at *
    linear_combination (B-C)^2*E
  · field_simp
    linear_combination E

theorem roots_regular {r:ℚ} (lo:0<r) (hi:r<1) :
    rightRoot r≠0 ∧ leftRoot r≠0 ∧ rightRoot r≠leftRoot r := by
  have B:0<rightRoot r:=by unfold rightRoot;positivity
  have C:0<leftRoot r:=by unfold leftRoot;positivity [sq_pos_of_ne_zero (sub_ne_zero.mpr hi.ne)]
  have gap:rightRoot r-leftRoot r=16*r:=by unfold rightRoot leftRoot;ring
  exact ⟨B.ne',C.ne',by intro e;rw [e,sub_self] at gap;linarith⟩

end
end Sun28.GlobalDescent
#print axioms Sun28.GlobalDescent.represented_iff
#print axioms Sun28.GlobalDescent.rescale
#print axioms Sun28.GlobalDescent.translate_zero
#print axioms Sun28.GlobalDescent.translate_minus
#print axioms Sun28.GlobalDescent.roots_regular
