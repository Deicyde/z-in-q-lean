import TorsionMarks

namespace Sun28.GlobalDescent
open Sun28.GlobalSections
noncomputable section

private theorem minus_step {B C d : ℚ} (B0:B≠0) (sep:B≠C) (d0:d≠0)
    (h:∃u y:ℚ,u≠0 ∧ y≠0 ∧ y^2=(d*u^2)*(d*u^2+B)*(d*u^2+C)) :
    ∃u y:ℚ,u≠0 ∧ y≠0 ∧ y^2=((-B*d)*u^2)*((-B*d)*u^2+B)*((-B*d)*u^2+C) := by
  obtain ⟨u,y,un,yn,E⟩:=h
  let x:=d*u^2
  have xn:x≠0:=mul_ne_zero d0 (pow_ne_zero 2 un)
  have e:y^2=x*(x+B)*(x+C):=E
  have xb:x+B≠0:=by
    intro zero;rw [zero,mul_zero,zero_mul] at e
    exact (pow_ne_zero 2 yn) e
  obtain ⟨vn,F,z⟩:=translate_minus B0 sep xb yn e
  let j:=y/((x+B)*d*u)
  have jn:j≠0:=div_ne_zero yn (mul_ne_zero (mul_ne_zero xb d0) un)
  have atx : -B*(x+C)/(x+B)=(-B*d)*j^2 := by
    apply mul_left_cancel₀ xn
    rw [z]
    dsimp [x,j]
    field_simp
  refine ⟨j,_,jn,vn,?_⟩
  rwa [←atx]

theorem orbit_right {r d:ℚ} (pos:0<r) (short:r<1) (dn:d≠0) (h:Mark r d) :
    Mark r (-rightRoot r*d) := by
  obtain ⟨bn,_,sep⟩:=roots_regular pos short
  exact minus_step bn sep dn h

theorem orbit_left {r d:ℚ} (pos:0<r) (short:r<1) (dn:d≠0) (h:Mark r d) :
    Mark r (-leftRoot r*d) := by
  obtain ⟨_,cn,sep⟩:=roots_regular pos short
  have flip (j:ℚ) : Mark r j ↔
      ∃u y:ℚ,u≠0 ∧ y≠0 ∧ y^2=(j*u^2)*(j*u^2+leftRoot r)*(j*u^2+rightRoot r) := by
    unfold Mark equation
    simp only [mul_right_comm]
  exact (flip _).mpr (minus_step cn sep.symm dn ((flip _).mp h))

theorem orbit_right_iff {r d:ℚ} (pos:0<r) (short:r<1) (dn:d≠0) :
    Mark r d ↔ Mark r (-rightRoot r*d) := by
  obtain ⟨bn,_,_⟩:=roots_regular pos short
  refine ⟨orbit_right pos short dn,fun h=> (rescale (r:=r) (d:=d) bn).mpr ?_⟩
  simpa only [neg_mul_neg,neg_mul,mul_neg,neg_neg,pow_two,mul_assoc,mul_left_comm,mul_comm]
    using orbit_right pos short (mul_ne_zero (neg_ne_zero.mpr bn) dn) h

theorem orbit_left_iff {r d:ℚ} (pos:0<r) (short:r<1) (dn:d≠0) :
    Mark r d ↔ Mark r (-leftRoot r*d) := by
  obtain ⟨_,cn,_⟩:=roots_regular pos short
  refine ⟨orbit_left pos short dn,fun h=> (rescale (r:=r) (d:=d) cn).mpr ?_⟩
  simpa only [neg_mul_neg,neg_mul,mul_neg,neg_neg,pow_two,mul_assoc,mul_left_comm,mul_comm]
    using orbit_left pos short (mul_ne_zero (neg_ne_zero.mpr cn) dn) h

theorem identity_class {r:ℚ} (lo:0<r) (hi:r<1) : Mark r 1 := by
  have nn:r-1≠0:=sub_ne_zero.mpr hi.ne
  have pp:0<r+1:=by linarith
  have yn:twiceY r≠0:=by unfold twiceY;positivity [sq_pos_of_ne_zero nn]
  exact ⟨r-1,twiceY r,nn,yn,by simpa only [one_mul,twiceX] using twice_on_curve r⟩

theorem moving_class {r:ℚ} (lo:0<r) (hi:r<1) : Mark r (lead r) := by
  have an:lead r≠0:=mul_ne_zero (sub_ne_zero.mpr hi.ne) (by linarith [lo] : r+3≠0)
  exact ⟨1,sectionY r,one_ne_zero,mul_ne_zero (mul_ne_zero (by norm_num) lo.ne') an,
    by simpa only [one_pow,mul_one,sectionX] using section_on_curve r⟩

end
end Sun28.GlobalDescent
#print axioms Sun28.GlobalDescent.orbit_right
#print axioms Sun28.GlobalDescent.orbit_left
#print axioms Sun28.GlobalDescent.orbit_right_iff
#print axioms Sun28.GlobalDescent.orbit_left_iff
#print axioms Sun28.GlobalDescent.identity_class
#print axioms Sun28.GlobalDescent.moving_class
