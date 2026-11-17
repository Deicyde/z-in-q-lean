import LocalKummerFibre
import ZInQKernel.RouteK.Selmer.Covering

namespace Sun28.MarkedOdd
open Sun28.SelmerRealization ZInQ.RouteK.Selmer
variable {K : Type*} [Field K] [CharZero K]

/-- The actual projective cover, including its chart at infinity. -/
theorem chart_of_cover {l : ℕ} {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Cover K l a b) :
    (SqEq (a:K) 1 ∧ SqEq (b:K) 1) ∨ ∃ x u v w : K,
       x=(a:K)*b*u^2 ∧ x-l=(b:K)*v^2 ∧ x+3*l=(a:K)*w^2 := by
  obtain ⟨X,Y,Z,T,h,e,f⟩ := h
  have an : (a:K) ≠ 0 := Int.cast_ne_zero.mpr ha
  have bn : (b:K) ≠ 0 := Int.cast_ne_zero.mpr hb
  by_cases t : T=0
  · subst T
    have E : (a:K)*X^2=Y^2 := by
      apply mul_left_cancel₀ bn
      linear_combination e
    have F : (b:K)*X^2=Z^2 := by
      apply mul_left_cancel₀ an
      linear_combination -f
    have xn : X≠0 := by
      rintro rfl
      simp only [ne_eq,not_true_eq_false,zero_pow (by decide : 2≠0),mul_zero,false_or,or_false] at h E F
      rcases h with hy|hz
      · exact (pow_ne_zero 2 hy) E.symm
      · exact (pow_ne_zero 2 hz) F.symm
    have yn : Y≠0 := fun H => (mul_ne_zero an (pow_ne_zero _ xn)) (by rw [E,H];ring)
    have zn : Z≠0 := fun H => (mul_ne_zero bn (pow_ne_zero _ xn)) (by rw [F,H];ring)
    left
    exact ⟨⟨Y/X,div_ne_zero yn xn,by field_simp;linear_combination E⟩,
      ⟨Z/X,div_ne_zero zn xn,by field_simp;linear_combination F⟩⟩
  · right
    refine ⟨(a:K)*b*(X/T)^2,X/T,Y/T,Z/T,rfl,?_,?_⟩
    · field_simp [t]
      linear_combination e
    · field_simp [t]
      linear_combination -f

omit [CharZero K] in
theorem class_of_equation {x z c r : K} (h : x=c*r^2) (hz : z≠0) (E : SqEq x z) : SqEq c z := by
  have hx := E.ne_zero hz
  have nr : r≠0 := fun hr => hx (by rw [h,hr];ring)
  exact (show SqEq x c from ⟨r,nr,h⟩).symm.trans E

omit [CharZero K] in
theorem square_product {l x A B u v w : K} (E : x=A*B*u^2)
    (F : x-l=B*v^2) (G : x+3*l=A*w^2) : IsSquare (x*(x-l)*(x+3*l)) := by
  refine ⟨A*B*u*v*w,?_⟩
  rw [G,F,E]
  ring

end Sun28.MarkedOdd
#print axioms Sun28.MarkedOdd.chart_of_cover
#print axioms Sun28.MarkedOdd.class_of_equation
#print axioms Sun28.MarkedOdd.square_product
